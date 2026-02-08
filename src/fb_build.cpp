// Fast Backend — AST walker: translates Odin AST into fast backend IR
//
// Mirrors the Tilde backend's cg_build_stmt / cg_build_expr pattern.

#include <setjmp.h>
#include <signal.h>

// Graceful fallback: catch assertion failures during procedure generation.
// When a proc uses unsupported features, the assert fires __builtin_trap()
// which raises SIGILL. We catch it and fall back to an empty stub.
gb_global thread_local sigjmp_buf fb_recovery_buf;
gb_global thread_local volatile bool fb_recovery_active = false;

gb_internal void fb_recovery_signal_handler(int sig) {
	if (fb_recovery_active) {
		fb_recovery_active = false;
		siglongjmp(fb_recovery_buf, 1);
	}
	// Not in recovery mode — re-raise for default behavior
	signal(sig, SIG_DFL);
	raise(sig);
}

// Forward declarations for mutually-referencing builder functions
gb_internal fbValue fb_build_expr(fbBuilder *b, Ast *expr);
gb_internal void    fb_build_stmt(fbBuilder *b, Ast *node);
gb_internal fbAddr  fb_build_compound_lit(fbBuilder *b, Ast *expr);
gb_internal void    fb_emit_defer_stmts(fbBuilder *b, fbDeferExitKind kind, i32 target_scope_index);

// ───────────────────────────────────────────────────────────────────────
// Parameter setup: classify params via ABI, create stack slots, record param_locs
// ───────────────────────────────────────────────────────────────────────

gb_internal void fb_setup_params(fbProc *p) {
	Type *pt = base_type(p->odin_type);
	GB_ASSERT(pt != nullptr && pt->kind == Type_Proc);

	TypeProc *proc_type = &pt->Proc;
	bool is_odin_cc = (proc_type->calling_convention == ProcCC_Odin);

	if (proc_type->params == nullptr && !is_odin_cc) {
		return;
	}

	i32 param_count = proc_type->param_count;

	// Determine split return count: for Odin CC with N results, the first
	// N-1 are returned via hidden output pointer parameters; the last is
	// returned in a register.
	TypeTuple *results = proc_type->results ? &proc_type->results->Tuple : nullptr;
	i32 result_count = results ? cast(i32)results->variables.count : 0;
	i32 split_count = (is_odin_cc && result_count > 1) ? (result_count - 1) : 0;

	u32 max_gp_params = param_count + split_count + (is_odin_cc ? 1 : 0);
	if (max_gp_params == 0 && param_count == 0) return;

	// Allocate for the hard upper bound on GP register params
	auto *locs = gb_alloc_array(heap_allocator(), fbProc::fbParamLoc, FB_X64_SYSV_MAX_GP_ARGS);

	// Allocate for XMM params (non-Odin CC only, max 8 XMM arg regs on SysV)
	auto *xmm_locs = gb_alloc_array(heap_allocator(), fbProc::fbXmmParamLoc, 8);

	// Allocate for stack-passed params (overflow beyond 6 GP registers).
	// Upper bound: 2 entries per param (two-eightbyte types) + split_count + 1 (context).
	u32 max_stack_params = cast(u32)(param_count * 2 + split_count + 1);
	auto *stack_locs = gb_alloc_array(heap_allocator(), fbProc::fbStackParamLoc, max_stack_params);

	u32 gp_idx = 0;
	u32 xmm_idx = 0;
	u32 stack_idx = 0;
	i32 stack_offset = 0; // byte offset from [RBP + 16]

	// Process declared parameters
	TypeTuple *params = proc_type->params ? &proc_type->params->Tuple : nullptr;
	for (i32 i = 0; i < param_count && params != nullptr; i++) {
		Entity *e = params->variables[i];
		if (e == nullptr || e->kind != Entity_Variable) continue;

		Type *param_type = e->type;
		fbABIParamInfo abi = fb_abi_classify_type_sysv(param_type);

		if (abi.num_classes == 0 || abi.classes[0] == FB_ABI_IGNORE) {
			continue;
		}

		if (abi.classes[0] == FB_ABI_MEMORY) {
			// MEMORY class: pass as a hidden pointer in a GP register.
			// The caller copies the value to a temp and passes the temp's address.
			if (gp_idx >= FB_X64_SYSV_MAX_GP_ARGS) {
				u32 slot = fb_slot_create(p, 8, 8, e, param_type);
				stack_locs[stack_idx].slot_idx       = slot;
				stack_locs[stack_idx].sub_offset      = 0;
				stack_locs[stack_idx].caller_offset   = stack_offset;
				stack_idx++;
				stack_offset += 8;
				continue;
			}
			u32 slot = fb_slot_create(p, 8, 8, e, param_type);
			locs[gp_idx].slot_idx   = slot;
			locs[gp_idx].sub_offset = 0;
			gp_idx++;
			continue;
		}

		if (abi.classes[0] == FB_ABI_SSE) {
			if (!is_odin_cc && xmm_idx < 8) {
				// Non-Odin CC (C/foreign): SSE params arrive in XMM0-7.
				// Create a stack slot and record XMM param location so
				// the prologue stores XMMn to the slot.
				fbType ft = fb_data_type(param_type);
				u32 slot = fb_slot_create(p, 8, 8, e, param_type);
				xmm_locs[xmm_idx].slot_idx    = slot;
				xmm_locs[xmm_idx].xmm_idx     = cast(u8)xmm_idx;
				xmm_locs[xmm_idx].float_kind   = ft.kind;
				xmm_idx++;
			} else {
				// Odin CC: route SSE through GP registers (internal convention)
				if (gp_idx >= FB_X64_SYSV_MAX_GP_ARGS) {
					u32 slot = fb_slot_create(p, 8, 8, e, param_type);
					stack_locs[stack_idx].slot_idx       = slot;
					stack_locs[stack_idx].sub_offset      = 0;
					stack_locs[stack_idx].caller_offset   = stack_offset;
					stack_idx++;
					stack_offset += 8;
				} else {
					u32 slot = fb_slot_create(p, 8, 8, e, param_type);
					locs[gp_idx].slot_idx   = slot;
					locs[gp_idx].sub_offset = 0;
					gp_idx++;
				}
			}
			continue;
		}

		// INTEGER class: each eightbyte consumes one GP register.
		// Two-eightbyte params (string, slice) get a single 16-byte slot;
		// single-eightbyte params get an 8-byte slot.
		if (abi.num_classes == 2 && abi.classes[0] == FB_ABI_INTEGER && abi.classes[1] == FB_ABI_INTEGER) {
			// The caller decomposes each eightbyte into a separate aux entry
			// and assigns them independently to registers or stack. Match that:
			// each eightbyte that doesn't fit in a register goes on the stack.
			u32 slot = fb_slot_create(p, 16, 8, e, param_type);
			// First eightbyte
			if (gp_idx < FB_X64_SYSV_MAX_GP_ARGS) {
				locs[gp_idx].slot_idx   = slot;
				locs[gp_idx].sub_offset = 0;
				gp_idx++;
			} else {
				stack_locs[stack_idx].slot_idx       = slot;
				stack_locs[stack_idx].sub_offset      = 0;
				stack_locs[stack_idx].caller_offset   = stack_offset;
				stack_idx++;
				stack_offset += 8;
			}
			// Second eightbyte
			if (gp_idx < FB_X64_SYSV_MAX_GP_ARGS) {
				locs[gp_idx].slot_idx   = slot;
				locs[gp_idx].sub_offset = 8;
				gp_idx++;
			} else {
				stack_locs[stack_idx].slot_idx       = slot;
				stack_locs[stack_idx].sub_offset      = 8;
				stack_locs[stack_idx].caller_offset   = stack_offset;
				stack_idx++;
				stack_offset += 8;
			}
		} else {
			if (gp_idx >= FB_X64_SYSV_MAX_GP_ARGS) {
				u32 slot = fb_slot_create(p, 8, 8, e, param_type);
				stack_locs[stack_idx].slot_idx       = slot;
				stack_locs[stack_idx].sub_offset      = 0;
				stack_locs[stack_idx].caller_offset   = stack_offset;
				stack_idx++;
				stack_offset += 8;
			} else {
				u32 slot = fb_slot_create(p, 8, 8, e, param_type);
				locs[gp_idx].slot_idx   = slot;
				locs[gp_idx].sub_offset = 0;
				gp_idx++;
			}
		}
	}

	// Odin CC multi-return: hidden output pointer params for values 0..N-2.
	// These go after regular params but before the context pointer, matching
	// the order the caller pushes them in fb_build_call_expr.
	if (split_count > 0) {
		p->split_returns_index = cast(i32)gp_idx;
		p->split_returns_count = 0;
		for (i32 i = 0; i < split_count; i++) {
			if (gp_idx >= FB_X64_SYSV_MAX_GP_ARGS) {
				// Split return pointers that overflow go on the stack
				u32 slot = fb_slot_create(p, 8, 8, nullptr, results->variables[i]->type);
				stack_locs[stack_idx].slot_idx       = slot;
				stack_locs[stack_idx].sub_offset      = 0;
				stack_locs[stack_idx].caller_offset   = stack_offset;
				stack_idx++;
				stack_offset += 8;
				p->split_returns_count++;
				continue;
			}
			// Each split return param is a pointer (8 bytes) to the caller's temp
			u32 slot = fb_slot_create(p, 8, 8, nullptr, results->variables[i]->type);
			locs[gp_idx].slot_idx   = slot;
			locs[gp_idx].sub_offset = 0;
			gp_idx++;
			p->split_returns_count++;
		}
	}

	// Odin CC: append context pointer as the last GP parameter
	if (is_odin_cc) {
		if (gp_idx < FB_X64_SYSV_MAX_GP_ARGS) {
			u32 slot = fb_slot_create(p, 8, 8, nullptr, nullptr);
			locs[gp_idx].slot_idx   = slot;
			locs[gp_idx].sub_offset = 0;
			gp_idx++;
		} else {
			u32 slot = fb_slot_create(p, 8, 8, nullptr, nullptr);
			stack_locs[stack_idx].slot_idx       = slot;
			stack_locs[stack_idx].sub_offset      = 0;
			stack_locs[stack_idx].caller_offset   = stack_offset;
			stack_idx++;
			stack_offset += 8;
		}
	}

	if (gp_idx > 0) {
		p->param_locs  = locs;
		p->param_count = gp_idx;
	} else {
		gb_free(heap_allocator(), locs);
	}

	if (xmm_idx > 0) {
		p->xmm_param_locs  = xmm_locs;
		p->xmm_param_count = xmm_idx;
	} else {
		gb_free(heap_allocator(), xmm_locs);
	}

	if (stack_idx > 0) {
		p->stack_param_locs  = stack_locs;
		p->stack_param_count = stack_idx;
	} else {
		gb_free(heap_allocator(), stack_locs);
	}
}

// ───────────────────────────────────────────────────────────────────────
// Entity → proc index map (built during first pass, used for SYMADDR/CALL)
// ───────────────────────────────────────────────────────────────────────

gb_global PtrMap<Entity *, u32> fb_entity_proc_map;
gb_global bool fb_entity_proc_map_inited = false;

// ───────────────────────────────────────────────────────────────────────
// Null-value sentinel for fbValue
// ───────────────────────────────────────────────────────────────────────

gb_internal bool fb_value_is_nil(fbValue v) {
	return v.id == FB_NOREG && v.type == nullptr;
}

gb_internal fbValue fb_value_nil(void) {
	fbValue v = {};
	v.id = FB_NOREG;
	v.type = nullptr;
	return v;
}

gb_internal fbValue fb_make_value(u32 id, Type *type) {
	fbValue v = {};
	v.id = id;
	v.type = type;
	return v;
}

// ───────────────────────────────────────────────────────────────────────
// Step 2: Builder instruction helpers
// ───────────────────────────────────────────────────────────────────────

gb_internal fbValue fb_emit(fbBuilder *b, fbOp op, fbType type, u32 a, u32 bb, u32 c, i64 imm) {
	u32 r = fb_inst_emit(b->proc, op, type, a, bb, c, 0, imm);
	return fb_make_value(r, nullptr);
}

gb_internal fbValue fb_emit_typed(fbBuilder *b, fbOp op, Type *odin_type, u32 a, u32 bb, u32 c, i64 imm) {
	fbType ft = fb_data_type(odin_type);
	u32 r = fb_inst_emit(b->proc, op, ft, a, bb, c, 0, imm);
	return fb_make_value(r, odin_type);
}

gb_internal fbValue fb_emit_iconst(fbBuilder *b, Type *type, i64 val) {
	fbType ft = fb_data_type(type);
	if (ft.kind == FBT_VOID) ft = FB_I64;
	// Mask to type width so the 64-bit representation matches what
	// LOAD produces via MOVZX (zero-extension is canonical form).
	switch (ft.kind) {
	case FBT_I1:  val &= 0x1; break;
	case FBT_I8:  val = cast(i64)(cast(u8)val); break;
	case FBT_I16: val = cast(i64)(cast(u16)val); break;
	case FBT_I32: val = cast(i64)(cast(u32)val); break;
	default: break;
	}
	u32 r = fb_inst_emit(b->proc, FB_ICONST, ft, FB_NOREG, FB_NOREG, FB_NOREG, 0, val);
	return fb_make_value(r, type);
}

gb_internal fbValue fb_emit_fconst(fbBuilder *b, Type *type, f64 val) {
	fbType ft = fb_data_type(type);
	if (ft.kind == FBT_VOID) ft = FB_F64;
	i64 bits;
	if (ft.kind == FBT_F32) {
		f32 f32val = cast(f32)val;
		gb_memmove(&bits, &f32val, 4);
		bits &= 0xFFFFFFFF;
	} else {
		gb_memmove(&bits, &val, 8);
	}
	u32 r = fb_inst_emit(b->proc, FB_FCONST, ft, FB_NOREG, FB_NOREG, FB_NOREG, 0, bits);
	return fb_make_value(r, type);
}

gb_internal fbValue fb_emit_load(fbBuilder *b, fbValue ptr, Type *elem_type) {
	fbType ft = fb_data_type(elem_type);
	if (ft.kind == FBT_VOID) ft = FB_I64; // aggregate: load as i64
	u32 r = fb_inst_emit(b->proc, FB_LOAD, ft, ptr.id, FB_NOREG, FB_NOREG, 0, 0);
	return fb_make_value(r, elem_type);
}

gb_internal void fb_emit_store(fbBuilder *b, fbValue ptr, fbValue val) {
	fbType ft = FB_I64;
	if (val.type != nullptr) {
		ft = fb_data_type(val.type);
		if (ft.kind == FBT_VOID) ft = FB_I64;
	}
	fb_inst_emit(b->proc, FB_STORE, ft, ptr.id, val.id, FB_NOREG, 0, 0);
}

gb_internal fbValue fb_emit_alloca_from_slot(fbBuilder *b, u32 slot_idx) {
	u32 r = fb_inst_emit(b->proc, FB_ALLOCA, FB_PTR, slot_idx, FB_NOREG, FB_NOREG, 0, 0);
	return fb_make_value(r, nullptr);
}

gb_internal void fb_emit_jump(fbBuilder *b, u32 target_block) {
	fb_inst_emit(b->proc, FB_JUMP, FB_VOID, target_block, FB_NOREG, FB_NOREG, 0, 0);
}

gb_internal void fb_emit_branch(fbBuilder *b, fbValue cond, u32 true_blk, u32 false_blk) {
	fb_inst_emit(b->proc, FB_BRANCH, FB_VOID, cond.id, true_blk, false_blk, 0, 0);
}

gb_internal void fb_emit_ret(fbBuilder *b, fbValue val) {
	fb_inst_emit(b->proc, FB_RET, FB_VOID, val.id, FB_NOREG, FB_NOREG, 0, 0);
}

gb_internal void fb_emit_ret_void(fbBuilder *b) {
	fb_inst_emit(b->proc, FB_RET, FB_VOID, FB_NOREG, FB_NOREG, FB_NOREG, 0, 0);
}

gb_internal fbValue fb_emit_arith(fbBuilder *b, fbOp op, fbValue lhs, fbValue rhs, Type *type) {
	fbType ft = fb_data_type(type);
	if (ft.kind == FBT_VOID) ft = FB_I64;
	u32 r = fb_inst_emit(b->proc, op, ft, lhs.id, rhs.id, FB_NOREG, 0, 0);
	return fb_make_value(r, type);
}

gb_internal fbValue fb_emit_cmp(fbBuilder *b, fbOp cmp_op, fbValue lhs, fbValue rhs) {
	// Store the operand type in imm so the lowerer can emit correctly-sized
	// comparisons. Float CMP needs this for ucomiss vs ucomisd. Signed integer
	// CMP needs this for type-width CMP encoding — without it, zero-extended
	// narrow values (e.g. i8(-1) = 0xFF) compare incorrectly under 64-bit CMP.
	i64 imm = 0;
	bool needs_operand_type = (cmp_op >= FB_CMP_FEQ && cmp_op <= FB_CMP_FGE)
	                       || (cmp_op >= FB_CMP_SLT && cmp_op <= FB_CMP_SGE);
	if (needs_operand_type) {
		Type *operand_type = lhs.type ? lhs.type : rhs.type;
		if (operand_type != nullptr) {
			imm = cast(i64)fb_type_pack(fb_data_type(operand_type));
		}
	}
	u32 r = fb_inst_emit(b->proc, cmp_op, FB_I1, lhs.id, rhs.id, FB_NOREG, 0, imm);
	return fb_make_value(r, t_bool);
}

gb_internal fbValue fb_emit_select(fbBuilder *b, fbValue cond, fbValue t, fbValue f, Type *type) {
	fbType ft = fb_data_type(type);
	if (ft.kind == FBT_VOID) ft = FB_I64;
	u32 r = fb_inst_emit(b->proc, FB_SELECT, ft, cond.id, t.id, f.id, 0, 0);
	return fb_make_value(r, type);
}

gb_internal void fb_emit_memzero(fbBuilder *b, fbValue ptr, i64 size, i64 align) {
	// Encoding: a=ptr, b=size_value, imm=alignment
	fbValue size_val = fb_emit_iconst(b, t_int, size);
	fb_inst_emit(b->proc, FB_MEMZERO, FB_VOID, ptr.id, size_val.id, FB_NOREG, 0, align);
}

gb_internal void fb_emit_memzero_v(fbBuilder *b, fbValue ptr, fbValue size, i64 align) {
	// Encoding: a=ptr, b=size_value, imm=alignment
	fb_inst_emit(b->proc, FB_MEMZERO, FB_VOID, ptr.id, size.id, FB_NOREG, 0, align);
}

gb_internal void fb_emit_memcpy(fbBuilder *b, fbValue dst, fbValue src, fbValue size, i64 align) {
	// Encoding: a=dst, b=src, c=size_value, imm=alignment
	fb_inst_emit(b->proc, FB_MEMCPY, FB_VOID, dst.id, src.id, size.id, 0, align);
}

gb_internal fbValue fb_emit_symaddr(fbBuilder *b, u32 sym_idx) {
	u32 r = fb_inst_emit(b->proc, FB_SYMADDR, FB_PTR, FB_NOREG, FB_NOREG, FB_NOREG, 0, cast(i64)sym_idx);
	return fb_make_value(r, nullptr);
}

gb_internal fbValue fb_emit_member(fbBuilder *b, fbValue base, i64 byte_offset) {
	u32 r = fb_inst_emit(b->proc, FB_MEMBER, FB_PTR, base.id, FB_NOREG, FB_NOREG, 0, byte_offset);
	return fb_make_value(r, nullptr);
}

gb_internal fbValue fb_emit_array_access(fbBuilder *b, fbValue base, fbValue index, i64 stride) {
	u32 r = fb_inst_emit(b->proc, FB_ARRAY, FB_PTR, base.id, index.id, FB_NOREG, 0, stride);
	return fb_make_value(r, nullptr);
}

// Create a new block and return its id (does NOT switch to it)
gb_internal u32 fb_new_block(fbBuilder *b) {
	return fb_block_create(b->proc);
}

// Switch the insertion point to a block
gb_internal void fb_set_block(fbBuilder *b, u32 block_id) {
	fb_block_start(b->proc, block_id);
	b->current_block = block_id;
}

// Check if the current block has a terminator (JUMP/BRANCH/RET/UNREACHABLE)
gb_internal bool fb_block_is_terminated(fbBuilder *b) {
	fbProc *p = b->proc;
	if (p->current_block >= p->block_count) return true;
	fbBlock *blk = &p->blocks[p->current_block];
	if (blk->inst_count == 0) return false;
	u32 last_idx = blk->first_inst + blk->inst_count - 1;
	u8 op = p->insts[last_idx].op;
	return op == FB_JUMP || op == FB_BRANCH || op == FB_RET ||
	       op == FB_UNREACHABLE || op == FB_SWITCH;
}

// ───────────────────────────────────────────────────────────────────────
// Step 3: Core builder functions
// ───────────────────────────────────────────────────────────────────────

// Determine if an Odin type is signed integer.
// Pointers, bitsets, and other non-integer types default to unsigned.
gb_internal bool fb_type_is_signed(Type *t) {
	t = core_type(t);
	if (t->kind == Type_Basic) {
		if (t->Basic.flags & BasicFlag_Boolean) return false;
		return (t->Basic.flags & BasicFlag_Unsigned) == 0;
	}
	if (t->kind == Type_Enum) {
		return fb_type_is_signed(t->Enum.base_type);
	}
	return false;
}

gb_internal fbValue fb_const_value(fbBuilder *b, Type *type, ExactValue value) {
	type = default_type(type);

	switch (value.kind) {
	case ExactValue_Bool:
		return fb_emit_iconst(b, type, value.value_bool ? 1 : 0);

	case ExactValue_Integer: {
		i64 ival = exact_value_to_i64(value);
		return fb_emit_iconst(b, type, ival);
	}

	case ExactValue_Float: {
		f64 fval = value.value_float;
		fbType ft = fb_data_type(type);
		if (fb_type_is_float(ft)) {
			return fb_emit_fconst(b, type, fval);
		}
		// Float used as integer (e.g. untyped constant in integer context)
		return fb_emit_iconst(b, type, cast(i64)fval);
	}

	case ExactValue_Pointer:
		return fb_emit_iconst(b, type, value.value_pointer);

	case ExactValue_Procedure: {
		Ast *proc_ast = value.value_procedure;
		if (proc_ast != nullptr) {
			Entity *e = entity_of_node(proc_ast);
			if (e != nullptr) {
				u32 *idx = map_get(&fb_entity_proc_map, e);
				if (idx != nullptr) {
					fbValue sym = fb_emit_symaddr(b, *idx);
					sym.type = type;
					return sym;
				}
			}
		}
		return fb_emit_iconst(b, type, 0);
	}

	case ExactValue_String: {
		String str = value.value_string;
		type = default_type(type);

		if (is_type_cstring(type)) {
			// cstring: just a pointer to the bytes
			u32 sym_idx = fb_module_intern_string_data(b->module, str);
			return fb_emit_symaddr(b, sym_idx);
		}

		// Odin string: {data: rawptr, len: int} — build on the stack
		i64 ptr_size = b->module->target.ptr_size;
		fbAddr s = fb_add_local(b, type, nullptr, false);

		if (str.len == 0) {
			// Empty string: zero-initialize
			fb_emit_memzero(b, s.base, type_size_of(type), type_align_of(type));
		} else {
			u32 sym_idx = fb_module_intern_string_data(b->module, str);
			fbValue data_ptr = fb_emit_symaddr(b, sym_idx);
			data_ptr.type = t_rawptr;

			// Store data pointer at offset 0
			fb_emit_store(b, s.base, data_ptr);
			// Store length at offset ptr_size
			fbValue len_val = fb_emit_iconst(b, t_int, str.len);
			fbValue len_ptr = fb_emit_member(b, s.base, ptr_size);
			fb_emit_store(b, len_ptr, len_val);
		}

		// Return pointer to the string struct (aggregate convention)
		s.base.type = type;
		return s.base;
	}

	case ExactValue_Complex:
	case ExactValue_Quaternion:
	case ExactValue_Typeid:
		GB_PANIC("fb_const_value: unhandled ExactValue kind %d", value.kind);
		return fb_value_nil();
	default:
		GB_PANIC("fb_const_value: unknown ExactValue kind %d", value.kind);
		return fb_value_nil();
	}
}

gb_internal fbAddr fb_add_local(fbBuilder *b, Type *type, Entity *entity, bool zero_init) {
	i64 size  = type_size_of(type);
	i64 align = type_align_of(type);
	if (size == 0) size = 1;
	if (align == 0) align = 1;

	u32 slot_idx = fb_slot_create(b->proc, cast(u32)size, cast(u32)align, entity, type);
	fbValue ptr = fb_emit_alloca_from_slot(b, slot_idx);

	if (zero_init) {
		fbType ft = fb_data_type(type);
		if (ft.kind != FBT_VOID && size <= 8) {
			// Scalar: store zero.
			// Float types use an integer type of matching width for the zero
			// store to avoid routing through FBT_F32/F64 STORE paths.
			Type *store_type = type;
			if (fb_type_is_float(ft)) {
				switch (ft.kind) {
				case FBT_F16: store_type = t_u16; break;
				case FBT_F32: store_type = t_u32; break;
				case FBT_F64: store_type = t_u64; break;
				default: break;
				}
			}
			fbValue zero = fb_emit_iconst(b, store_type, 0);
			fb_emit_store(b, ptr, zero);
		} else if (size > 0) {
			// Aggregate: memzero
			fb_emit_memzero(b, ptr, size, align);
		}
	}

	fbAddr addr = {};
	addr.kind = fbAddr_Default;
	addr.base = ptr;
	addr.type = type;

	if (entity != nullptr) {
		map_set(&b->variable_map, entity, addr);
	}

	return addr;
}

gb_internal fbValue fb_addr_load(fbBuilder *b, fbAddr addr) {
	if (addr.kind == fbAddr_Default) {
		// Aggregates (strings, slices, structs): return the pointer.
		// The caller is responsible for decomposing into scalar loads
		// when needed (e.g., for ABI register passing).
		fbType ft = fb_data_type(addr.type);
		if (ft.kind == FBT_VOID) {
			fbValue ptr = addr.base;
			ptr.type = addr.type;
			return ptr;
		}
		return fb_emit_load(b, addr.base, addr.type);
	}
	GB_PANIC("TODO fb_addr_load kind=%d", addr.kind);
	return fb_value_nil();
}

gb_internal void fb_addr_store(fbBuilder *b, fbAddr addr, fbValue val) {
	if (addr.kind == fbAddr_Default) {
		fb_emit_store(b, addr.base, val);
		return;
	}
	GB_PANIC("TODO fb_addr_store kind=%d", addr.kind);
}

// Store a value into a destination pointer. For scalar types, emits a STORE.
// For aggregate types (structs, arrays, etc.), emits a MEMCPY from the source
// pointer to the destination. The val parameter is a scalar value for scalar
// types, or a pointer to the aggregate data for aggregate types.
gb_internal void fb_emit_copy_value(fbBuilder *b, fbValue dst_ptr, fbValue val, Type *type) {
	fbType ft = fb_data_type(type);
	if (ft.kind != FBT_VOID) {
		// Scalar: direct store
		fb_emit_store(b, dst_ptr, val);
	} else {
		// Aggregate: val is a pointer to data, use memcpy
		i64 size  = type_size_of(type);
		i64 align = type_align_of(type);
		if (size > 0) {
			fbValue size_val = fb_emit_iconst(b, t_int, size);
			fb_emit_memcpy(b, dst_ptr, val, size_val, align);
		}
	}
}

// Store a variant value into a union, writing both the data and the tag.
// union_ptr points to the union memory.  variant_val is the variant data
// (scalar value or pointer-to-aggregate, as per fb_emit_copy_value convention).
gb_internal void fb_emit_store_union_variant(fbBuilder *b, fbValue union_ptr, fbValue variant_val,
                                             Type *union_type, Type *variant_type) {
	union_type = base_type(union_type);
	GB_ASSERT(union_type->kind == Type_Union);

	if (is_type_union_maybe_pointer(union_type) || type_size_of(union_type) == 0) {
		// Maybe-pointer union or zero-size union: just store the data, no tag.
		fb_emit_copy_value(b, union_ptr, variant_val, variant_type);
		return;
	}

	// Store variant data at offset 0 (reinterpret union ptr as variant ptr).
	if (type_size_of(variant_type) == 0) {
		// Zero-sized variant: clear the data area so stale data doesn't linger.
		i64 block_size = union_type->Union.variant_block_size.load(std::memory_order_relaxed);
		if (block_size > 0) {
			fb_emit_memzero(b, union_ptr, block_size, 1);
		}
	} else {
		fbValue data_ptr = union_ptr;
		data_ptr.type = alloc_type_pointer(variant_type);
		fb_emit_copy_value(b, data_ptr, variant_val, variant_type);
	}

	// Store the tag.
	type_size_of(union_type); // ensure layout is cached
	i64 tag_offset = union_type->Union.variant_block_size.load(std::memory_order_relaxed);
	Type *tag_type = union_tag_type(union_type);
	i64 tag_val = union_variant_index(union_type, variant_type);

	fbValue tag_ptr = fb_emit_member(b, union_ptr, tag_offset);
	fbValue tag_const = fb_emit_iconst(b, tag_type, tag_val);
	fb_emit_store(b, tag_ptr, tag_const);
}

// Load a field from an aggregate in memory.
// base_ptr points to the start of the aggregate; field is at byte_offset.
gb_internal fbValue fb_load_field(fbBuilder *b, fbValue base_ptr, i64 byte_offset, Type *field_type) {
	fbValue ptr = base_ptr;
	if (byte_offset != 0) {
		ptr = fb_emit_member(b, base_ptr, byte_offset);
	}
	return fb_emit_load(b, ptr, field_type);
}

gb_internal fbAddr fb_make_global_addr(fbBuilder *b, Entity *e, u32 gidx) {
	u32 abstract_sym = FB_GLOBAL_SYM_BASE + gidx;
	fbValue ptr = fb_emit_symaddr(b, abstract_sym);
	ptr.type = alloc_type_pointer(e->type);
	fbAddr addr = {};
	addr.kind = fbAddr_Default;
	addr.base = ptr;
	addr.type = e->type;
	return addr;
}

// ── Synthetic C library calls ─────────────────────────────────────────
//
// Some operations (string comparison, struct equality) need libc functions
// like memcmp. These aren't declared in user code, so we lazily create
// foreign proc entries that the ELF emitter writes as undefined symbols
// for the linker to resolve.

gb_internal u32 fb_ensure_c_proc(fbModule *m, String name) {
	// Check if already added.
	for_array(i, m->procs) {
		if (str_eq(m->procs[i]->name, name)) {
			return cast(u32)i;
		}
	}
	// Create a minimal foreign proc.
	fbProc *p = gb_alloc_item(permanent_allocator(), fbProc);
	gb_zero_item(p);
	p->name = name;
	p->is_foreign = true;
	p->current_block = FB_NOREG;
	p->split_returns_index = -1;

	u32 idx = cast(u32)m->procs.count;
	array_add(&m->procs, p);
	return idx;
}

// Emit a C calling convention call with pre-built argument values.
// Arguments must already be scalar (GP or SSE), not aggregates.
gb_internal fbValue fb_emit_call_c(fbBuilder *b, u32 proc_idx, fbValue *args, u32 arg_count, fbType ret_ft, Type *ret_type) {
	fbValue target = fb_emit_symaddr(b, proc_idx);

	u32 aux_start = b->proc->aux_count;
	for (u32 i = 0; i < arg_count; i++) {
		fb_aux_push(b->proc, args[i].id);
	}

	u32 r = fb_inst_emit(b->proc, FB_CALL, ret_ft, target.id, aux_start, arg_count, 0, 0);
	// Patch CC to C.
	fbInst *call_inst = &b->proc->insts[b->proc->inst_count - 1];
	call_inst->flags = FBCC_C;

	return fb_make_value(r, ret_type);
}

gb_internal fbAddr fb_build_addr(fbBuilder *b, Ast *expr) {
	expr = unparen_expr(expr);

	switch (expr->kind) {
	case Ast_Ident: {
		Entity *e = entity_of_node(expr);
		if (e != nullptr) {
			e = strip_entity_wrapping(e);
			fbAddr *found = map_get(&b->variable_map, e);
			if (found != nullptr) {
				return *found;
			}

			// Global variable reference
			if (e->kind == Entity_Variable) {
				u32 *gidx = map_get(&b->module->global_entity_map, e);
				if (gidx != nullptr) {
					return fb_make_global_addr(b, e, *gidx);
				}
			}
		}
		GB_PANIC("fb_build_addr Ident: entity not found for '%s'", expr_to_string(expr));
		break;
	}

	case Ast_DerefExpr: {
		fbValue ptr = fb_build_expr(b, expr->DerefExpr.expr);
		Type *elem = type_deref(type_of_expr(expr));
		fbAddr addr = {};
		addr.kind = fbAddr_Default;
		addr.base = ptr;
		addr.type = elem;
		return addr;
	}

	case Ast_SelectorExpr: {
		ast_node(se, SelectorExpr, expr);
		Entity *e = entity_of_node(se->selector);
		if (e == nullptr) {
			GB_PANIC("fb_build_addr SelectorExpr: null entity");
		}

		// Check if it's in the variable_map (e.g., for using declarations)
		fbAddr *found = map_get(&b->variable_map, e);
		if (found != nullptr) {
			return *found;
		}

		Selection sel = lookup_field(type_of_expr(se->expr), e->token.string, false);
		fbAddr base_addr = fb_build_addr(b, se->expr);
		fbValue base_ptr = base_addr.base;

		// Walk the selection path.
		// type_offset_of() handles structs, basic struct-like types
		// (any, string), slices, dynamic arrays, tuples, and unions.
		Type *current_type = base_addr.type;
		for_array(i, sel.index) {
			i32 field_idx = sel.index[i];
			Type *bt = base_type(current_type);
			if (is_type_pointer(bt)) {
				base_ptr = fb_emit_load(b, base_ptr, current_type);
				current_type = type_deref(current_type);
				bt = base_type(current_type);
			}
			Type *field_type = nullptr;
			i64 offset = type_offset_of(bt, field_idx, &field_type);
			if (offset != 0) {
				base_ptr = fb_emit_member(b, base_ptr, offset);
			}
			if (field_type != nullptr) {
				current_type = field_type;
			} else if (bt->kind == Type_Struct) {
				current_type = bt->Struct.fields[field_idx]->type;
			}
		}

		Type *result_type = e->type;
		fbAddr addr = {};
		addr.kind = fbAddr_Default;
		addr.base = base_ptr;
		addr.type = result_type;
		return addr;
	}

	case Ast_IndexExpr: {
		ast_node(ie, IndexExpr, expr);
		fbAddr base_addr = fb_build_addr(b, ie->expr);
		fbValue index = fb_build_expr(b, ie->index);

		Type *bt = base_type(base_addr.type);
		Type *elem_type = nullptr;
		i64 stride = 0;

		fbValue data_ptr = base_addr.base;

		if (bt->kind == Type_Array) {
			elem_type = bt->Array.elem;
			stride = type_size_of(elem_type);
		} else if (bt->kind == Type_Slice) {
			// Slice: load .data pointer (field 0, offset 0)
			elem_type = bt->Slice.elem;
			stride = type_size_of(elem_type);
			data_ptr = fb_emit_load(b, base_addr.base, t_rawptr);
		} else if (bt->kind == Type_DynamicArray) {
			// Dynamic array: load .data pointer (field 0, offset 0)
			elem_type = bt->DynamicArray.elem;
			stride = type_size_of(elem_type);
			data_ptr = fb_emit_load(b, base_addr.base, t_rawptr);
		} else if (is_type_string(bt)) {
			// String: load .data pointer (field 0, offset 0), element is u8
			elem_type = t_u8;
			stride = 1;
			data_ptr = fb_emit_load(b, base_addr.base, t_rawptr);
		} else if (is_type_pointer(bt) || is_type_multi_pointer(bt)) {
			elem_type = type_deref(base_addr.type);
			stride = type_size_of(elem_type);
		} else {
			elem_type = type_of_expr(expr);
			stride = type_size_of(elem_type);
		}

		fbValue ptr = fb_emit_array_access(b, data_ptr, index, stride);
		fbAddr addr = {};
		addr.kind = fbAddr_Default;
		addr.base = ptr;
		addr.type = elem_type;
		return addr;
	}

	case Ast_UnaryExpr: {
		if (expr->UnaryExpr.op.kind == Token_And) {
			return fb_build_addr(b, expr->UnaryExpr.expr);
		}
		break;
	}

	case Ast_Implicit: {
		ast_node(im, Implicit, expr);
		if (im->kind == Token_context) {
			if (b->context_stack.count == 0) {
				// Non-Odin-CC proc referencing `context` — auto-create one.
				// Mirrors lb_find_or_generate_context_ptr().
				fbAddr ctx_addr = fb_add_local(b, t_context, nullptr, true);

				fbContextData *cd = array_add_and_get(&b->context_stack);
				cd->ctx = ctx_addr;
				cd->uses_default = false;
			}
			return b->context_stack[b->context_stack.count - 1].ctx;
		}
		break;
	}

	case Ast_CompoundLit:
		return fb_build_compound_lit(b, expr);

	case Ast_SliceExpr: {
		ast_node(se, SliceExpr, expr);
		i64 ptr_size = b->module->target.ptr_size;

		fbValue low  = fb_emit_iconst(b, t_int, 0);
		fbValue high = {};

		if (se->low  != nullptr) low  = fb_build_expr(b, se->low);
		if (se->high != nullptr) high = fb_build_expr(b, se->high);

		fbAddr base_addr = fb_build_addr(b, se->expr);
		Type *bt = base_type(base_addr.type);

		// Pointer to container: dereference
		if (is_type_pointer(bt)) {
			base_addr.base = fb_emit_load(b, base_addr.base, base_addr.type);
			base_addr.type = type_deref(base_addr.type);
			bt = base_type(base_addr.type);
		}

		fbValue data_ptr = {};
		i64 stride = 0;
		Type *result_type = nullptr;

		if (bt->kind == Type_Array) {
			// Array: base is already data pointer, element type from array
			data_ptr = base_addr.base;
			stride = type_size_of(bt->Array.elem);
			result_type = alloc_type_slice(bt->Array.elem);
			if (high.type == nullptr) {
				high = fb_emit_iconst(b, t_int, bt->Array.count);
			}
		} else if (bt->kind == Type_Slice) {
			data_ptr = fb_emit_load(b, base_addr.base, t_rawptr);
			stride = type_size_of(bt->Slice.elem);
			result_type = base_addr.type;
			if (high.type == nullptr) {
				high = fb_load_field(b, base_addr.base, ptr_size, t_int);
			}
		} else if (is_type_string(bt)) {
			data_ptr = fb_emit_load(b, base_addr.base, t_rawptr);
			stride = 1; // u8
			result_type = t_string;
			if (high.type == nullptr) {
				high = fb_load_field(b, base_addr.base, ptr_size, t_int);
			}
		} else if (bt->kind == Type_DynamicArray) {
			data_ptr = fb_emit_load(b, base_addr.base, t_rawptr);
			stride = type_size_of(bt->DynamicArray.elem);
			result_type = alloc_type_slice(bt->DynamicArray.elem);
			if (high.type == nullptr) {
				high = fb_load_field(b, base_addr.base, ptr_size, t_int);
			}
		} else if (bt->kind == Type_MultiPointer) {
			// Multi-pointer [^]T: the value itself is a pointer to T
			data_ptr = fb_emit_load(b, base_addr.base, t_rawptr);
			stride = type_size_of(bt->MultiPointer.elem);
			result_type = alloc_type_slice(bt->MultiPointer.elem);
			// No implicit high bound — caller must provide high
		} else {
			GB_PANIC("fb_build_addr SliceExpr: unhandled base type %s", type_to_string(bt));
		}

		// elem = data_ptr + low * stride
		fbValue elem = fb_emit_array_access(b, data_ptr, low, stride);
		// new_len = high - low
		fbValue new_len = fb_emit_arith(b, FB_SUB, high, low, t_int);

		// Build result slice: {rawptr, int}
		fbAddr result = fb_add_local(b, result_type, nullptr, false);
		fb_emit_store(b, result.base, elem);
		fbValue len_ptr = fb_emit_member(b, result.base, ptr_size);
		fb_emit_store(b, len_ptr, new_len);
		return result;
	}

	default:
		break;
	}

	GB_PANIC("TODO fb_build_addr %.*s", LIT(ast_strings[expr->kind]));
	return {};
}

gb_internal fbValue fb_emit_conv(fbBuilder *b, fbValue val, Type *dst_type) {
	if (val.type == nullptr || dst_type == nullptr) return val;

	Type *src_type = val.type;
	if (are_types_identical(src_type, dst_type)) return val;

	// ── any boxing: value → any ─────────────────────────────────
	if (is_type_any(dst_type)) {
		if (is_type_untyped_uninit(src_type) || is_type_untyped_nil(src_type)) {
			fbAddr temp = fb_add_local(b, dst_type, nullptr, true);
			fbValue result = temp.base;
			result.type = dst_type;
			return result;
		}

		Type *st = default_type(src_type);

		// Get a pointer to the source value.
		fbValue data_ptr;
		fbType src_ft = fb_data_type(st);
		if (src_ft.kind == FBT_VOID) {
			// Aggregate: val is already a pointer to stable memory.
			data_ptr = val;
			data_ptr.type = t_rawptr;
		} else {
			// Scalar: materialize to a stack slot, take its address.
			fbAddr temp_val = fb_add_local(b, st, nullptr, false);
			fb_emit_store(b, temp_val.base, val);
			data_ptr = temp_val.base;
			data_ptr.type = t_rawptr;
		}

		// Compute typeid (compile-time constant hash).
		u64 typeid_value = type_hash_canonical_type(st);
		fbValue id_val = fb_emit_iconst(b, t_typeid, cast(i64)typeid_value);

		// Build the any struct on the stack: {data: rawptr, id: typeid}
		fbAddr any_addr = fb_add_local(b, dst_type, nullptr, true);
		i64 ptr_sz = build_context.ptr_size;

		fbValue data_field = fb_emit_member(b, any_addr.base, 0);
		fb_emit_store(b, data_field, data_ptr);

		fbValue id_field = fb_emit_member(b, any_addr.base, ptr_sz);
		fb_emit_store(b, id_field, id_val);

		fbValue result = any_addr.base;
		result.type = dst_type;
		return result;
	}

	// ── Union conversion: value → union ─────────────────────────
	if (is_type_union(base_type(dst_type))) {
		Type *union_type = base_type(dst_type);
		Type *variant_type = src_type;
		// Find the matching variant type in the union.
		for (Type *vt : union_type->Union.variants) {
			if (are_types_identical(base_type(src_type), base_type(vt))) {
				variant_type = vt;
				break;
			}
			if (internal_check_is_assignable_to(src_type, vt)) {
				variant_type = vt;
				break;
			}
		}
		fbAddr temp = fb_add_local(b, dst_type, nullptr, true);
		val = fb_emit_conv(b, val, variant_type);
		fb_emit_store_union_variant(b, temp.base, val, union_type, variant_type);
		// Unions are aggregates — return pointer.
		fbValue result = temp.base;
		result.type = dst_type;
		return result;
	}

	fbType src_ft = fb_data_type(src_type);
	fbType dst_ft = fb_data_type(dst_type);

	// ── Scalar → Aggregate (nil literal) ────────────────────────
	// The only way to reach scalar→aggregate conversion is through nil
	// literals (Odin doesn't allow implicit scalar-to-aggregate casts).
	// Allocate a zero-initialized local of the destination type.
	if (dst_ft.kind == FBT_VOID && src_ft.kind != FBT_VOID) {
		fbAddr temp = fb_add_local(b, dst_type, nullptr, true);
		fbValue result = temp.base;
		result.type = dst_type;
		return result;
	}

	if (fb_type_eq(src_ft, dst_ft)) {
		// Same machine type, just rebrand
		val.type = dst_type;
		return val;
	}

	i32 src_size = fb_type_size(src_ft);
	i32 dst_size = fb_type_size(dst_ft);

	// ── Bool conversions ─────────────────────────────────────────
	// FBT_I1 is included in fb_type_is_integer(), so bool-specific
	// paths must precede the general integer/float paths to get the
	// correct semantics: ZEXT (not SEXT), and compare (not truncate).

	// Bool → Integer: always zero-extend (bool is inherently unsigned)
	if (src_ft.kind == FBT_I1 && fb_type_is_integer(dst_ft)) {
		u32 r = fb_inst_emit(b->proc, FB_ZEXT, dst_ft, val.id, FB_NOREG, FB_NOREG, 0, cast(i64)fb_type_pack(src_ft));
		return fb_make_value(r, dst_type);
	}

	// Integer → Bool: nonzero test (truncation would only check the low bit)
	if (fb_type_is_integer(src_ft) && dst_ft.kind == FBT_I1) {
		fbValue zero = fb_emit_iconst(b, src_type, 0);
		return fb_emit_cmp(b, FB_CMP_NE, val, zero);
	}

	// Bool → Float: zero-extend to i32 first, then unsigned int-to-float
	if (src_ft.kind == FBT_I1 && fb_type_is_float(dst_ft)) {
		u32 ext = fb_inst_emit(b->proc, FB_ZEXT, FB_I32, val.id, FB_NOREG, FB_NOREG, 0, cast(i64)fb_type_pack(src_ft));
		u32 r = fb_inst_emit(b->proc, FB_UI2FP, dst_ft, ext, FB_NOREG, FB_NOREG, 0, cast(i64)fb_type_pack(FB_I32));
		return fb_make_value(r, dst_type);
	}

	// Float → Bool: nonzero test (FP2SI truncation loses fractional values)
	if (fb_type_is_float(src_ft) && dst_ft.kind == FBT_I1) {
		fbValue zero = fb_emit_fconst(b, src_type, 0.0);
		return fb_emit_cmp(b, FB_CMP_FNE, val, zero);
	}

	// ── General conversions ──────────────────────────────────────

	// Integer → Integer
	if (fb_type_is_integer(src_ft) && fb_type_is_integer(dst_ft)) {
		if (dst_size > src_size) {
			// Extend
			fbOp op = fb_type_is_signed(src_type) ? FB_SEXT : FB_ZEXT;
			u32 r = fb_inst_emit(b->proc, op, dst_ft, val.id, FB_NOREG, FB_NOREG, 0, cast(i64)fb_type_pack(src_ft));
			return fb_make_value(r, dst_type);
		} else if (dst_size < src_size) {
			// Truncate
			u32 r = fb_inst_emit(b->proc, FB_TRUNC, dst_ft, val.id, FB_NOREG, FB_NOREG, 0, cast(i64)fb_type_pack(src_ft));
			return fb_make_value(r, dst_type);
		}
		// Same size, just rebrand
		val.type = dst_type;
		return val;
	}

	// Pointer → Pointer (no-op at IR level)
	if (src_ft.kind == FBT_PTR && dst_ft.kind == FBT_PTR) {
		val.type = dst_type;
		return val;
	}

	// Pointer → Integer
	if (src_ft.kind == FBT_PTR && fb_type_is_integer(dst_ft)) {
		u32 r = fb_inst_emit(b->proc, FB_PTR2INT, dst_ft, val.id, FB_NOREG, FB_NOREG, 0, 0);
		return fb_make_value(r, dst_type);
	}

	// Integer → Pointer
	if (fb_type_is_integer(src_ft) && dst_ft.kind == FBT_PTR) {
		u32 r = fb_inst_emit(b->proc, FB_INT2PTR, FB_PTR, val.id, FB_NOREG, FB_NOREG, 0, 0);
		return fb_make_value(r, dst_type);
	}

	// Float → Float
	if (fb_type_is_float(src_ft) && fb_type_is_float(dst_ft)) {
		fbOp op = (dst_size > src_size) ? FB_FPEXT : FB_FPTRUNC;
		u32 r = fb_inst_emit(b->proc, op, dst_ft, val.id, FB_NOREG, FB_NOREG, 0, cast(i64)fb_type_pack(src_ft));
		return fb_make_value(r, dst_type);
	}

	// Integer → Float
	if (fb_type_is_integer(src_ft) && fb_type_is_float(dst_ft)) {
		fbOp op = fb_type_is_signed(src_type) ? FB_SI2FP : FB_UI2FP;
		u32 r = fb_inst_emit(b->proc, op, dst_ft, val.id, FB_NOREG, FB_NOREG, 0, cast(i64)fb_type_pack(src_ft));
		return fb_make_value(r, dst_type);
	}

	// Float → Integer
	if (fb_type_is_float(src_ft) && fb_type_is_integer(dst_ft)) {
		fbOp op = fb_type_is_signed(dst_type) ? FB_FP2SI : FB_FP2UI;
		u32 r = fb_inst_emit(b->proc, op, dst_ft, val.id, FB_NOREG, FB_NOREG, 0, cast(i64)fb_type_pack(src_ft));
		return fb_make_value(r, dst_type);
	}

	// Same-size bitcast
	if (src_size == dst_size && src_size > 0) {
		u32 r = fb_inst_emit(b->proc, FB_BITCAST, dst_ft, val.id, FB_NOREG, FB_NOREG, 0, 0);
		return fb_make_value(r, dst_type);
	}

	GB_PANIC("fb_emit_conv: unhandled conversion from %d to %d", src_ft.kind, dst_ft.kind);
	return fb_value_nil();
}

// ───────────────────────────────────────────────────────────────────────
// Step 3b: Compound literal builder
// ───────────────────────────────────────────────────────────────────────

gb_internal void fb_build_compound_lit_struct(fbBuilder *b, Ast *expr, Type *bt, fbValue dst_ptr) {
	ast_node(cl, CompoundLit, expr);
	TypeStruct *st = &bt->Struct;

	for_array(field_index, cl->elems) {
		Ast *elem = cl->elems[field_index];
		Ast *value_expr = nullptr;
		isize index = field_index;

		if (elem->kind == Ast_FieldValue) {
			ast_node(fv, FieldValue, elem);
			String name = fv->field->Ident.token.string;
			Selection sel = lookup_field(bt, name, false);
			GB_ASSERT_MSG(!sel.indirect,
				"compound literal field '%.*s' requires indirect access", LIT(name));

			value_expr = fv->value;

			// Deep field path (e.g. using/embedded struct): walk the selection
			if (sel.index.count > 1) {
				fbValue ptr = dst_ptr;
				Type *current_type = bt;
				for_array(si, sel.index) {
					i32 idx = sel.index[si];
					Type *ct = base_type(current_type);
					GB_ASSERT(ct->kind == Type_Struct);
					i64 offset = ct->Struct.offsets[idx];
					if (offset != 0) {
						ptr = fb_emit_member(b, ptr, offset);
					}
					current_type = ct->Struct.fields[idx]->type;
				}
				fbValue val = fb_build_expr(b, value_expr);
				val = fb_emit_conv(b, val, sel.entity->type);
				fb_emit_copy_value(b, ptr, val, sel.entity->type);
				continue;
			}

			index = sel.index[0];
		} else {
			// Positional field: use the entity's field_index to get the
			// correct structural position (handles using/embedded fields).
			Selection sel = lookup_field_from_index(bt, st->fields[field_index]->Variable.field_index);
			GB_ASSERT(sel.index.count == 1);
			GB_ASSERT(!sel.indirect);
			index = sel.index[0];
			value_expr = elem;
		}

		Entity *field = st->fields[index];
		Type *field_type = field->type;

		fbValue val = fb_build_expr(b, value_expr);
		val = fb_emit_conv(b, val, field_type);

		// Compute field pointer
		fbValue field_ptr = dst_ptr;
		i64 offset = st->offsets[index];
		if (offset != 0) {
			field_ptr = fb_emit_member(b, dst_ptr, offset);
		}

		fb_emit_copy_value(b, field_ptr, val, field_type);
	}
}

gb_internal void fb_build_compound_lit_array(fbBuilder *b, Ast *expr, Type *bt, fbValue dst_ptr) {
	ast_node(cl, CompoundLit, expr);
	Type *elem_type = bt->Array.elem;
	i64 stride = type_size_of(elem_type);

	for_array(i, cl->elems) {
		Ast *elem = cl->elems[i];
		Ast *value_expr = nullptr;
		i64 elem_index = cast(i64)i;

		if (elem->kind == Ast_FieldValue) {
			ast_node(fv, FieldValue, elem);

			if (is_ast_range(fv->field)) {
				// Range initialization: lo..hi = value  or  lo..<hi = value
				ast_node(ie, BinaryExpr, fv->field);
				TypeAndValue lo_tav = ie->left->tav;
				TypeAndValue hi_tav = ie->right->tav;
				GB_ASSERT(lo_tav.mode == Addressing_Constant);
				GB_ASSERT(hi_tav.mode == Addressing_Constant);

				i64 lo = exact_value_to_i64(lo_tav.value);
				i64 hi = exact_value_to_i64(hi_tav.value);
				if (ie->op.kind != Token_RangeHalf) {
					hi += 1;
				}

				fbValue val = fb_build_expr(b, fv->value);
				val = fb_emit_conv(b, val, elem_type);

				for (i64 k = lo; k < hi; k++) {
					i64 byte_offset = k * stride;
					fbValue elem_ptr = (byte_offset == 0) ? dst_ptr : fb_emit_member(b, dst_ptr, byte_offset);
					fb_emit_copy_value(b, elem_ptr, val, elem_type);
				}
				continue;
			}

			// Indexed initialization: [idx] = value
			TypeAndValue idx_tav = fv->field->tav;
			GB_ASSERT(idx_tav.mode == Addressing_Constant);
			elem_index = exact_value_to_i64(idx_tav.value);
			value_expr = fv->value;
		} else {
			value_expr = elem;
		}

		fbValue val = fb_build_expr(b, value_expr);
		val = fb_emit_conv(b, val, elem_type);

		i64 byte_offset = elem_index * stride;
		fbValue elem_ptr = (byte_offset == 0) ? dst_ptr : fb_emit_member(b, dst_ptr, byte_offset);
		fb_emit_copy_value(b, elem_ptr, val, elem_type);
	}
}

gb_internal void fb_build_compound_lit_enumerated_array(fbBuilder *b, Ast *expr, Type *bt, fbValue dst_ptr) {
	ast_node(cl, CompoundLit, expr);
	Type *elem_type = bt->EnumeratedArray.elem;
	i64 stride = type_size_of(elem_type);
	i64 index_offset = exact_value_to_i64(*bt->EnumeratedArray.min_value);

	for_array(i, cl->elems) {
		Ast *elem = cl->elems[i];
		Ast *value_expr = nullptr;
		i64 elem_index = cast(i64)i;

		if (elem->kind == Ast_FieldValue) {
			ast_node(fv, FieldValue, elem);
			TypeAndValue idx_tav = fv->field->tav;
			GB_ASSERT(idx_tav.mode == Addressing_Constant);
			elem_index = exact_value_to_i64(idx_tav.value) - index_offset;
			value_expr = fv->value;
		} else {
			value_expr = elem;
		}

		fbValue val = fb_build_expr(b, value_expr);
		val = fb_emit_conv(b, val, elem_type);

		i64 byte_offset = elem_index * stride;
		fbValue elem_ptr = (byte_offset == 0) ? dst_ptr : fb_emit_member(b, dst_ptr, byte_offset);
		fb_emit_copy_value(b, elem_ptr, val, elem_type);
	}
}

// Build a compound literal into a stack-allocated temporary.
// Returns an fbAddr pointing to the filled-in aggregate.
gb_internal fbAddr fb_build_compound_lit(fbBuilder *b, Ast *expr) {
	Type *type = type_of_expr(expr);
	Type *bt = base_type(type);

	// Allocate and zero-initialize a temp for the compound literal
	fbAddr v = fb_add_local(b, type, nullptr, true);

	ast_node(cl, CompoundLit, expr);
	if (cl->elems.count == 0) {
		// Empty compound literal: zero-init is sufficient
		return v;
	}

	switch (bt->kind) {
	case Type_Struct:
		fb_build_compound_lit_struct(b, expr, bt, v.base);
		break;

	case Type_Array:
		fb_build_compound_lit_array(b, expr, bt, v.base);
		break;

	case Type_EnumeratedArray:
		fb_build_compound_lit_enumerated_array(b, expr, bt, v.base);
		break;

	case Type_Union: {
		// Union compound literal: Value{variant_value}
		// The checker resolves the single element to the correct variant type.
		GB_ASSERT(cl->elems.count == 1);
		Ast *elem = cl->elems[0];
		Ast *value_expr = elem;
		if (elem->kind == Ast_FieldValue) {
			value_expr = elem->FieldValue.value;
		}
		fbValue val = fb_build_expr(b, value_expr);
		Type *variant_type = type_of_expr(value_expr);
		fb_emit_store_union_variant(b, v.base, val, bt, variant_type);
		break;
	}

	default:
		GB_PANIC("fast backend: compound literal for type kind %d not yet supported (%s)",
			bt->kind, type_to_string(type));
		break;
	}

	return v;
}

// ───────────────────────────────────────────────────────────────────────
// Step 4: Expression builder
// ───────────────────────────────────────────────────────────────────────

gb_internal fbValue fb_build_binary_expr(fbBuilder *b, Ast *expr) {
	ast_node(be, BinaryExpr, expr);

	TypeAndValue tv = type_and_value_of_expr(expr);
	Type *type = default_type(tv.type);

	switch (be->op.kind) {
	case Token_Add:
	case Token_Sub:
	case Token_Mul:
	case Token_Quo:
	case Token_Mod:
	case Token_And:
	case Token_Or:
	case Token_Xor:
	case Token_AndNot:
	case Token_Shl:
	case Token_Shr: {
		fbValue left  = fb_build_expr(b, be->left);
		fbValue right = fb_build_expr(b, be->right);

		bool is_float = fb_type_is_float(fb_data_type(type));
		fbOp op;
		switch (be->op.kind) {
		case Token_Add: op = is_float ? FB_FADD : FB_ADD; break;
		case Token_Sub: op = is_float ? FB_FSUB : FB_SUB; break;
		case Token_Mul: op = is_float ? FB_FMUL : FB_MUL; break;
		case Token_Quo:
			op = is_float ? FB_FDIV : (fb_type_is_signed(type) ? FB_SDIV : FB_UDIV);
			break;
		case Token_Mod:
			op = fb_type_is_signed(type) ? FB_SMOD : FB_UMOD;
			break;
		case Token_And:    op = FB_AND; break;
		case Token_Or:     op = FB_OR;  break;
		case Token_Xor:    op = FB_XOR; break;
		case Token_AndNot: {
			// a &~ b => a & (~b)
			fbType ft = fb_data_type(type);
			if (ft.kind == FBT_VOID) ft = FB_I64;
			u32 not_r = fb_inst_emit(b->proc, FB_NOT, ft, right.id, FB_NOREG, FB_NOREG, 0, 0);
			return fb_emit_arith(b, FB_AND, left, fb_make_value(not_r, type), type);
		}
		case Token_Shl: op = FB_SHL; break;
		case Token_Shr:
			op = fb_type_is_signed(type) ? FB_ASHR : FB_LSHR;
			break;
		default: GB_PANIC("unreachable"); op = FB_ADD; break;
		}

		return fb_emit_arith(b, op, left, right, type);
	}

	case Token_CmpEq:
	case Token_NotEq:
	case Token_Lt:
	case Token_LtEq:
	case Token_Gt:
	case Token_GtEq: {
		fbValue left  = fb_build_expr(b, be->left);
		fbValue right = fb_build_expr(b, be->right);

		Type *operand_type = left.type ? left.type : type;

		// String comparison via memcmp.
		// Strings are {data: rawptr, len: int}. For equality: compare
		// lengths first, then byte content. For ordering: lexicographic
		// comparison via memcmp with length tie-break.
		if (is_type_string(operand_type) && !is_type_cstring(operand_type)) {
			i64 ptr_size = b->module->target.ptr_size;
			u32 memcmp_idx = fb_ensure_c_proc(b->module, str_lit("memcmp"));

			fbValue a_data = fb_load_field(b, left,  0,        t_rawptr);
			fbValue a_len  = fb_load_field(b, left,  ptr_size, t_int);
			fbValue b_data = fb_load_field(b, right, 0,        t_rawptr);
			fbValue b_len  = fb_load_field(b, right, ptr_size, t_int);

			u32 tmp_slot = fb_slot_create(b->proc, 1, 1, nullptr, t_bool);
			fbValue tmp_ptr = fb_emit_alloca_from_slot(b, tmp_slot);

			bool is_eq  = (be->op.kind == Token_CmpEq);
			bool is_neq = (be->op.kind == Token_NotEq);

			if (is_eq || is_neq) {
				//   entry:       branch len_eq -> check_zero, short_out
				//   short_out:   store !eq, jump merge
				//   check_zero:  branch len==0 -> trivial, do_cmp
				//   trivial:     store eq, jump merge
				//   do_cmp:      r=memcmp; store (r==0 for eq, r!=0 for neq); jump merge
				//   merge:       load result
				u32 short_out  = fb_new_block(b);
				u32 check_zero = fb_new_block(b);
				u32 trivial    = fb_new_block(b);
				u32 do_cmp     = fb_new_block(b);
				u32 merge      = fb_new_block(b);

				fbValue len_eq = fb_emit_cmp(b, FB_CMP_EQ, a_len, b_len);
				fb_emit_branch(b, len_eq, check_zero, short_out);

				fb_set_block(b, short_out);
				fb_emit_store(b, tmp_ptr, fb_emit_iconst(b, t_bool, is_neq ? 1 : 0));
				fb_emit_jump(b, merge);

				fb_set_block(b, check_zero);
				fbValue len_zero = fb_emit_cmp(b, FB_CMP_EQ, a_len, fb_emit_iconst(b, t_int, 0));
				fb_emit_branch(b, len_zero, trivial, do_cmp);

				fb_set_block(b, trivial);
				fb_emit_store(b, tmp_ptr, fb_emit_iconst(b, t_bool, is_eq ? 1 : 0));
				fb_emit_jump(b, merge);

				fb_set_block(b, do_cmp);
				fbValue args[3] = {a_data, b_data, a_len};
				fbValue r = fb_emit_call_c(b, memcmp_idx, args, 3, FB_I32, t_i32);
				fbValue zero_i32 = fb_emit_iconst(b, t_i32, 0);
				fbValue cmp = fb_emit_cmp(b, is_eq ? FB_CMP_EQ : FB_CMP_NE, r, zero_i32);
				fb_emit_store(b, tmp_ptr, cmp);
				fb_emit_jump(b, merge);

				fb_set_block(b, merge);
				return fb_emit_conv(b, fb_emit_load(b, tmp_ptr, t_bool), type);
			}

			// Ordering: <, <=, >, >=
			//   entry:       min_len = select(a<b, a, b); branch min_len!=0 -> do_cmp, len_only
			//   do_cmp:      r=memcmp; branch r!=0 -> byte_decide, len_only
			//   byte_decide: store (r<0 for </<=, r>0 for >/>=); jump merge
			//   len_only:    store (a_len <op> b_len); jump merge
			//   merge:       load result
			u32 do_cmp      = fb_new_block(b);
			u32 byte_decide = fb_new_block(b);
			u32 len_only    = fb_new_block(b);
			u32 merge       = fb_new_block(b);

			fbValue a_shorter = fb_emit_cmp(b, FB_CMP_ULT, a_len, b_len);
			fbValue min_len = fb_emit_select(b, a_shorter, a_len, b_len, t_int);
			fbValue min_nz = fb_emit_cmp(b, FB_CMP_NE, min_len, fb_emit_iconst(b, t_int, 0));
			fb_emit_branch(b, min_nz, do_cmp, len_only);

			fb_set_block(b, do_cmp);
			fbValue args[3] = {a_data, b_data, min_len};
			fbValue r = fb_emit_call_c(b, memcmp_idx, args, 3, FB_I32, t_i32);
			fbValue r_nz = fb_emit_cmp(b, FB_CMP_NE, r, fb_emit_iconst(b, t_i32, 0));
			fb_emit_branch(b, r_nz, byte_decide, len_only);

			fb_set_block(b, byte_decide);
			fbValue zero_i32 = fb_emit_iconst(b, t_i32, 0);
			bool use_lt = (be->op.kind == Token_Lt || be->op.kind == Token_LtEq);
			fbValue byte_cmp = fb_emit_cmp(b, use_lt ? FB_CMP_SLT : FB_CMP_SGT, r, zero_i32);
			fb_emit_store(b, tmp_ptr, byte_cmp);
			fb_emit_jump(b, merge);

			fb_set_block(b, len_only);
			fbOp len_op;
			switch (be->op.kind) {
			case Token_Lt:   len_op = FB_CMP_ULT; break;
			case Token_LtEq: len_op = FB_CMP_ULE; break;
			case Token_Gt:   len_op = FB_CMP_UGT; break;
			default:         len_op = FB_CMP_UGE; break;
			}
			fbValue len_cmp = fb_emit_cmp(b, len_op, a_len, b_len);
			fb_emit_store(b, tmp_ptr, len_cmp);
			fb_emit_jump(b, merge);

			fb_set_block(b, merge);
			return fb_emit_conv(b, fb_emit_load(b, tmp_ptr, t_bool), type);
		}

		bool is_float = fb_type_is_float(fb_data_type(operand_type));
		bool is_signed = fb_type_is_signed(operand_type);

		fbOp op;
		if (is_float) {
			switch (be->op.kind) {
			case Token_CmpEq: op = FB_CMP_FEQ; break;
			case Token_NotEq: op = FB_CMP_FNE; break;
			case Token_Lt:    op = FB_CMP_FLT; break;
			case Token_LtEq:  op = FB_CMP_FLE; break;
			case Token_Gt:    op = FB_CMP_FGT; break;
			case Token_GtEq:  op = FB_CMP_FGE; break;
			default: GB_PANIC("unreachable"); op = FB_CMP_FEQ; break;
			}
		} else {
			switch (be->op.kind) {
			case Token_CmpEq: op = FB_CMP_EQ; break;
			case Token_NotEq: op = FB_CMP_NE; break;
			case Token_Lt:    op = is_signed ? FB_CMP_SLT : FB_CMP_ULT; break;
			case Token_LtEq:  op = is_signed ? FB_CMP_SLE : FB_CMP_ULE; break;
			case Token_Gt:    op = is_signed ? FB_CMP_SGT : FB_CMP_UGT; break;
			case Token_GtEq:  op = is_signed ? FB_CMP_SGE : FB_CMP_UGE; break;
			default: GB_PANIC("unreachable"); op = FB_CMP_EQ; break;
			}
		}

		fbValue cmp = fb_emit_cmp(b, op, left, right);
		return fb_emit_conv(b, cmp, type);
	}

	case Token_CmpAnd:
	case Token_CmpOr: {
		// Short-circuit evaluation using a temp alloca to avoid
		// cross-block SELECT referencing values from skipped blocks.
		u32 rhs_block   = fb_new_block(b);
		u32 short_block = fb_new_block(b);
		u32 done_block  = fb_new_block(b);

		// Allocate a temp slot to hold the boolean result
		u32 tmp_slot = fb_slot_create(b->proc, 1, 1, nullptr, t_bool);
		fbValue tmp_ptr = fb_emit_alloca_from_slot(b, tmp_slot);

		fbValue left = fb_build_expr(b, be->left);
		fbValue left_bool = fb_emit_conv(b, left, t_bool);

		if (be->op.kind == Token_CmpAnd) {
			// CmpAnd: if left then evaluate right, else result is false
			fb_emit_branch(b, left_bool, rhs_block, short_block);

			// Short-circuit block: store false
			fb_set_block(b, short_block);
			fbValue false_val = fb_emit_iconst(b, t_bool, 0);
			fb_emit_store(b, tmp_ptr, false_val);
			fb_emit_jump(b, done_block);

			// RHS block: evaluate right, store result
			fb_set_block(b, rhs_block);
			fbValue right = fb_build_expr(b, be->right);
			fbValue right_bool = fb_emit_conv(b, right, t_bool);
			right_bool.type = t_bool;
			fb_emit_store(b, tmp_ptr, right_bool);
			fb_emit_jump(b, done_block);
		} else {
			// CmpOr: if left then result is true, else evaluate right
			fb_emit_branch(b, left_bool, short_block, rhs_block);

			// Short-circuit block: store true
			fb_set_block(b, short_block);
			fbValue true_val = fb_emit_iconst(b, t_bool, 1);
			fb_emit_store(b, tmp_ptr, true_val);
			fb_emit_jump(b, done_block);

			// RHS block: evaluate right, store result
			fb_set_block(b, rhs_block);
			fbValue right = fb_build_expr(b, be->right);
			fbValue right_bool = fb_emit_conv(b, right, t_bool);
			right_bool.type = t_bool;
			fb_emit_store(b, tmp_ptr, right_bool);
			fb_emit_jump(b, done_block);
		}

		// Done block: load result from the temp alloca
		fb_set_block(b, done_block);
		fbValue result = fb_emit_load(b, tmp_ptr, t_bool);
		return fb_emit_conv(b, result, type);
	}

	default:
		GB_PANIC("TODO fb_build_binary_expr op=%d", be->op.kind);
		break;
	}

	return fb_value_nil();
}

gb_internal fbValue fb_build_unary_expr(fbBuilder *b, Ast *expr) {
	ast_node(ue, UnaryExpr, expr);
	Type *type = type_of_expr(expr);

	switch (ue->op.kind) {
	case Token_Sub: {
		fbValue val = fb_build_expr(b, ue->expr);
		fbType ft = fb_data_type(type);
		if (ft.kind == FBT_VOID) ft = FB_I64;
		fbOp neg_op = fb_type_is_float(ft) ? FB_FNEG : FB_NEG;
		u32 r = fb_inst_emit(b->proc, neg_op, ft, val.id, FB_NOREG, FB_NOREG, 0, 0);
		return fb_make_value(r, type);
	}
	case Token_Xor: {
		// Bitwise complement
		fbValue val = fb_build_expr(b, ue->expr);
		fbType ft = fb_data_type(type);
		if (ft.kind == FBT_VOID) ft = FB_I64;
		u32 r = fb_inst_emit(b->proc, FB_NOT, ft, val.id, FB_NOREG, FB_NOREG, 0, 0);
		return fb_make_value(r, type);
	}
	case Token_Not: {
		// Logical not: compare with zero
		fbValue val = fb_build_expr(b, ue->expr);
		fbValue zero = fb_emit_iconst(b, val.type ? val.type : type, 0);
		return fb_emit_cmp(b, FB_CMP_EQ, val, zero);
	}
	default:
		GB_PANIC("TODO fb_build_unary_expr op=%d", ue->op.kind);
		break;
	}

	return fb_value_nil();
}

// Build a Source_Code_Location struct value on the stack.
// Layout: {file_path: string, line: i32, column: i32, procedure: string} = 40 bytes.
gb_internal fbValue fb_build_source_code_location(fbBuilder *b, String proc_name, TokenPos pos) {
	String file = get_file_path_string(pos.file_id);
	String procedure = proc_name;
	i32 line   = pos.line;
	i32 column = pos.column;

	switch (build_context.source_code_location_info) {
	case SourceCodeLocationInfo_Normal:
	case SourceCodeLocationInfo_Obfuscated: // TODO: proper obfuscation
	case SourceCodeLocationInfo_Filename:
		break;
	case SourceCodeLocationInfo_None:
		file = str_lit("");
		procedure = str_lit("");
		line = 0;
		column = 0;
		break;
	}

	i64 ptr_size = b->module->target.ptr_size;

	// Allocate the struct on the stack (40 bytes on 64-bit)
	fbAddr loc = fb_add_local(b, t_source_code_location, nullptr, false);

	// file_path string at offset 0: {data: rawptr, len: int}
	if (file.len > 0) {
		u32 sym_idx = fb_module_intern_string_data(b->module, file);
		fbValue file_ptr = fb_emit_symaddr(b, sym_idx);
		file_ptr.type = t_rawptr;
		fb_emit_store(b, loc.base, file_ptr);
		fbValue file_len = fb_emit_iconst(b, t_int, file.len);
		fbValue len_ptr = fb_emit_member(b, loc.base, ptr_size);
		fb_emit_store(b, len_ptr, file_len);
	} else {
		fb_emit_memzero(b, loc.base, 2 * ptr_size, ptr_size);
	}

	// line: i32 at offset 16
	fbValue line_ptr = fb_emit_member(b, loc.base, 2 * ptr_size);
	fbValue line_val = fb_emit_iconst(b, t_i32, line);
	fb_emit_store(b, line_ptr, line_val);

	// column: i32 at offset 20
	fbValue col_ptr = fb_emit_member(b, loc.base, 2 * ptr_size + 4);
	fbValue col_val = fb_emit_iconst(b, t_i32, column);
	fb_emit_store(b, col_ptr, col_val);

	// procedure string at offset 24: {data: rawptr, len: int}
	fbValue proc_field = fb_emit_member(b, loc.base, 2 * ptr_size + 8);
	if (procedure.len > 0) {
		u32 proc_sym_idx = fb_module_intern_string_data(b->module, procedure);
		fbValue proc_ptr = fb_emit_symaddr(b, proc_sym_idx);
		proc_ptr.type = t_rawptr;
		fb_emit_store(b, proc_field, proc_ptr);
		fbValue proc_len = fb_emit_iconst(b, t_int, procedure.len);
		fbValue proc_len_ptr = fb_emit_member(b, proc_field, ptr_size);
		fb_emit_store(b, proc_len_ptr, proc_len);
	} else {
		fb_emit_memzero(b, proc_field, 2 * ptr_size, ptr_size);
	}

	loc.base.type = t_source_code_location;
	return loc.base;
}

// Handle a default parameter value for a call argument.
gb_internal fbValue fb_handle_param_value(fbBuilder *b, Type *param_type, ParameterValue const &pv, Ast *call_expr) {
	switch (pv.kind) {
	case ParameterValue_Constant:
		return fb_const_value(b, param_type, pv.value);

	case ParameterValue_Nil: {
		// Zero-initialized value of the parameter type
		fbAddr nil_val = fb_add_local(b, param_type, nullptr, true);
		nil_val.base.type = param_type;
		return nil_val.base;
	}

	case ParameterValue_Location: {
		String proc_name = {};
		if (b->entity != nullptr) {
			proc_name = b->entity->token.string;
		}
		ast_node(ce, CallExpr, call_expr);
		TokenPos pos = ast_token(ce->proc).pos;
		return fb_build_source_code_location(b, proc_name, pos);
	}

	case ParameterValue_Expression: {
		Ast *orig = pv.original_ast_expr;
		if (orig != nullptr) {
			return fb_build_expr(b, orig);
		}
		// Fallthrough to zero
		fbAddr nil_val = fb_add_local(b, param_type, nullptr, true);
		nil_val.base.type = param_type;
		return nil_val.base;
	}

	default:
		GB_PANIC("fb_handle_param_value: unhandled kind %d", pv.kind);
		return fb_value_nil();
	}
}

gb_internal fbValue fb_build_call_expr(fbBuilder *b, Ast *expr) {
	ast_node(ce, CallExpr, expr);

	// Build callee
	fbValue target = fb_build_expr(b, ce->proc);

	// Determine calling convention and return info
	Type *proc_type = type_of_expr(ce->proc);
	if (proc_type != nullptr) {
		proc_type = base_type(proc_type);
	}
	bool is_odin_cc = false;
	TypeTuple *results = nullptr;
	i32 result_count = 0;

	if (proc_type != nullptr && proc_type->kind == Type_Proc) {
		is_odin_cc = (proc_type->Proc.calling_convention == ProcCC_Odin);
		if (proc_type->Proc.results != nullptr) {
			results = &proc_type->Proc.results->Tuple;
			result_count = cast(i32)results->variables.count;
		}
	}

	// For Odin CC: values passed via hidden output pointers.
	// Multi-return: values 0..N-2 get split temps.
	// Single-return MEMORY-class: the sole result also needs a temp.
	i32 split_count = (is_odin_cc && result_count > 1) ? (result_count - 1) : 0;
	fbAddr *split_temps = nullptr;
	bool sret_single = false; // single MEMORY-class return via hidden output pointer
	fbAddr sret_temp = {};

	if (split_count > 0) {
		split_temps = gb_alloc_array(heap_allocator(), fbAddr, split_count);
		for (i32 i = 0; i < split_count; i++) {
			split_temps[i] = fb_add_local(b, results->variables[i]->type, nullptr, true);
		}
	}

	// Check if the last/sole return type is MEMORY class (large aggregate).
	// For single return: the sole result needs sret hidden output pointer.
	// Applies to all calling conventions: Odin, contextless, C, etc.
	if (!sret_single && result_count >= 1 && split_count == 0) {
		Type *ret_type = results->variables[result_count - 1]->type;
		fbABIParamInfo ret_abi = fb_abi_classify_type_sysv(ret_type);
		if (ret_abi.classes[0] == FB_ABI_MEMORY) {
			sret_single = true;
			sret_temp = fb_add_local(b, ret_type, nullptr, true);
		}
	}

	// Phase 1: Evaluate all argument expressions (explicit + defaults).
	// This must happen before capturing aux_start because argument
	// expressions may contain nested calls which push their own aux entries.
	TypeTuple *params = nullptr;
	isize param_count = 0;
	if (proc_type != nullptr && proc_type->kind == Type_Proc && proc_type->Proc.params != nullptr) {
		params = &proc_type->Proc.params->Tuple;
		param_count = params->variables.count;
	}

	struct fbBuiltArg { fbValue val; Type *type; };
	isize arg_expr_count = ce->args.count;
	isize total_arg_count = gb_max(arg_expr_count, param_count);
	fbBuiltArg *built_args = nullptr;
	if (total_arg_count > 0) {
		built_args = gb_alloc_array(heap_allocator(), fbBuiltArg, total_arg_count);

		// Build explicit positional arguments
		for_array(i, ce->args) {
			built_args[i].val  = fb_build_expr(b, ce->args[i]);
			built_args[i].type = type_of_expr(ce->args[i]);
		}

		// Fill default values for any missing parameters
		for (isize i = arg_expr_count; i < param_count; i++) {
			Entity *e = params->variables[i];
			if (e->kind == Entity_Variable && has_parameter_value(e->Variable.param_value)) {
				built_args[i].val = fb_handle_param_value(b, e->type, e->Variable.param_value, expr);
				built_args[i].type = e->type;
			} else if (e->kind == Entity_Constant) {
				built_args[i].val = fb_const_value(b, e->type, e->Constant.value);
				built_args[i].type = e->type;
			} else if (e->kind == Entity_TypeName) {
				// Type params are erased at runtime — pass nil
				built_args[i].val = fb_emit_iconst(b, t_rawptr, 0);
				built_args[i].type = e->type;
			} else {
				// Unknown default — zero-initialize
				fbAddr nil_val = fb_add_local(b, e->type, nullptr, true);
				nil_val.base.type = e->type;
				built_args[i].val = nil_val.base;
				built_args[i].type = e->type;
			}
		}
	}
	arg_expr_count = total_arg_count;

	// Phase 2: Push arguments into aux pool. No nested calls occur here,
	// so aux_start accurately marks the beginning of this call's args.
	u32 aux_start = b->proc->aux_count;

	// Track SSE argument bitmasks for C-ABI calls.
	// Bit N in sse_mask: aux entry N is an SSE (float) arg.
	// Bit N in f64_mask: that SSE arg is f64 (vs f32).
	u32 sse_mask = 0;
	u32 f64_mask = 0;
	u32 aux_idx = 0;

	// Regular arguments — decompose 2-eightbyte types (string, slice, any)
	// into two scalar values for SysV register passing.
	for (isize i = 0; i < arg_expr_count; i++) {
		fbValue arg = built_args[i].val;
		Type *arg_type = built_args[i].type;

		fbABIParamInfo abi = {};
		if (arg_type != nullptr) {
			abi = fb_abi_classify_type_sysv(default_type(arg_type));
		}

		if (abi.num_classes == 2 && abi.classes[0] == FB_ABI_INTEGER && abi.classes[1] == FB_ABI_INTEGER) {
			// Two-eightbyte type: arg is a pointer to the struct.
			// Load each 8-byte half as a separate scalar value.
			i64 ptr_size = b->module->target.ptr_size;
			fbValue lo = fb_emit_load(b, arg, t_rawptr);
			fbValue hi_ptr = fb_emit_member(b, arg, ptr_size);
			fbValue hi = fb_emit_load(b, hi_ptr, t_int);
			fb_aux_push(b->proc, lo.id);
			fb_aux_push(b->proc, hi.id);
			aux_idx += 2;
		} else if (abi.num_classes == 1 && abi.classes[0] == FB_ABI_INTEGER &&
		           arg_type != nullptr && fb_data_type(default_type(arg_type)).kind == FBT_VOID) {
			// Small aggregate (struct/array <= 8 bytes) classified as 1xINTEGER.
			// arg is a pointer to the aggregate; load as a scalar integer.
			i64 agg_sz = type_size_of(core_type(default_type(arg_type)));
			Type *load_type;
			if (agg_sz <= 1) load_type = t_u8;
			else if (agg_sz <= 2) load_type = t_u16;
			else if (agg_sz <= 4) load_type = t_u32;
			else load_type = t_u64;
			fbValue val = fb_emit_load(b, arg, load_type);
			fb_aux_push(b->proc, val.id);
			aux_idx++;
		} else {
			if (!is_odin_cc && abi.num_classes >= 1 && abi.classes[0] == FB_ABI_SSE && aux_idx < 32) {
				sse_mask |= (1u << aux_idx);
				fbType ft = fb_data_type(default_type(arg_type));
				if (ft.kind == FBT_F64) {
					f64_mask |= (1u << aux_idx);
				}
			}
			fb_aux_push(b->proc, arg.id);
			aux_idx++;
		}
	}

	if (built_args != nullptr) {
		gb_free(heap_allocator(), built_args);
	}

	// Split return output pointers (Odin CC multi-return, values 0..N-2)
	for (i32 i = 0; i < split_count; i++) {
		fb_aux_push(b->proc, split_temps[i].base.id);
	}
	// Single MEMORY-class return: pass hidden output pointer
	if (sret_single) {
		fb_aux_push(b->proc, sret_temp.base.id);
	}

	// Context pointer (Odin CC, always last)
	if (is_odin_cc) {
		if (b->context_stack.count == 0) {
			// Non-Odin-CC proc calling an Odin-CC proc — auto-create context.
			fbAddr ctx_addr = fb_add_local(b, t_context, nullptr, true);
			fbContextData *cd = array_add_and_get(&b->context_stack);
			cd->ctx = ctx_addr;
			cd->uses_default = false;
		}
		fbContextData *ctx = &b->context_stack[b->context_stack.count - 1];
		fbValue ctx_ptr = fb_addr_load(b, ctx->ctx);
		fb_aux_push(b->proc, ctx_ptr.id);
	}

	u32 arg_count = b->proc->aux_count - aux_start;

	// Return type is the last result (Odin CC) or the sole result
	Type *last_result_type = nullptr;
	fbType ret_ft = FB_VOID;
	if (result_count > 0) {
		if (is_odin_cc) {
			last_result_type = results->variables[result_count - 1]->type;
		} else {
			Type *rt = proc_type->Proc.results;
			if (rt->kind == Type_Tuple) {
				GB_ASSERT_MSG(rt->Tuple.variables.count == 1,
					"fast backend: multi-return not yet supported for non-Odin CC (got %td results)",
					rt->Tuple.variables.count);
				last_result_type = rt->Tuple.variables[0]->type;
			} else {
				last_result_type = rt;
			}
		}
		ret_ft = fb_data_type(last_result_type);
	}

	// Encode calling convention and SSE bitmasks into the call instruction.
	// flags = calling convention (0=Odin, 1=C, ...)
	// imm = sse_mask (low 32) | f64_mask (high 32)
	u8 cc_flag = is_odin_cc ? FBCC_ODIN : FBCC_C;
	i64 call_imm = cast(i64)sse_mask | (cast(i64)f64_mask << 32);

	// For sret_single, the call itself is void — the result is in the temp
	fbType emit_ret_ft = sret_single ? FB_VOID : ret_ft;
	u32 r = fb_inst_emit(b->proc, FB_CALL, emit_ret_ft, target.id, aux_start, arg_count, 0, 0);
	// Patch flags and imm after emit (fb_inst_emit sets them to 0)
	{
		fbInst *call_inst = &b->proc->insts[b->proc->inst_count - 1];
		call_inst->flags = cc_flag;
		call_inst->imm   = call_imm;
	}
	fbValue last_val;
	if (sret_single) {
		// Return the pointer to the temp where the callee wrote the result
		last_val = sret_temp.base;
		last_val.type = last_result_type;
	} else {
		last_val = fb_make_value(r, last_result_type);
	}

	// Expose split return temps so the statement-level handler can unpack them
	b->last_call_split_temps = split_temps;
	b->last_call_split_count = split_count;

	return last_val;
}

// Load the hidden output pointer for the i-th split return value.
// Split returns first fill GP param slots starting at split_returns_index;
// any that overflow beyond FB_X64_SYSV_MAX_GP_ARGS go to stack_param_locs.
gb_internal fbValue fb_load_split_return_ptr(fbBuilder *b, i32 i) {
	i32 param_idx = b->proc->split_returns_index + i;
	if (param_idx < cast(i32)b->proc->param_count) {
		u32 slot_idx = b->proc->param_locs[param_idx].slot_idx;
		fbValue slot_ptr = fb_emit_alloca_from_slot(b, slot_idx);
		return fb_emit_load(b, slot_ptr, t_rawptr);
	}
	// Overflowed to stack — scan stack_param_locs for split return entries.
	// Split return pointers have entity==NULL and odin_type!=NULL.
	i32 gp_split_count = cast(i32)b->proc->param_count - b->proc->split_returns_index;
	if (gp_split_count < 0) gp_split_count = 0;
	i32 stack_split_idx = i - gp_split_count;
	i32 found = 0;
	for (u32 si = 0; si < b->proc->stack_param_count; si++) {
		u32 slot_idx = b->proc->stack_param_locs[si].slot_idx;
		fbStackSlot *slot = &b->proc->slots[slot_idx];
		if (slot->entity == nullptr && slot->odin_type != nullptr) {
			if (found == stack_split_idx) {
				fbValue slot_ptr = fb_emit_alloca_from_slot(b, slot_idx);
				return fb_emit_load(b, slot_ptr, t_rawptr);
			}
			found++;
		}
	}
	GB_PANIC("fast backend: could not find stack slot for split return %d", i);
	return {};
}

// Unpack a multi-return call into individual values.
// out_values must have space for out_count elements.
gb_internal void fb_unpack_multi_return(fbBuilder *b, fbValue last_val, fbValue *out_values, i32 out_count) {
	i32 split_count = b->last_call_split_count;

	// Load each split return value from its temp
	for (i32 i = 0; i < split_count && i < out_count; i++) {
		out_values[i] = fb_addr_load(b, b->last_call_split_temps[i]);
	}

	// The last return value was returned in a register
	if (split_count < out_count) {
		out_values[split_count] = last_val;
	}

	// Clean up
	if (b->last_call_split_temps != nullptr) {
		gb_free(heap_allocator(), b->last_call_split_temps);
		b->last_call_split_temps = nullptr;
		b->last_call_split_count = 0;
	}
}

gb_internal fbValue fb_build_expr(fbBuilder *b, Ast *expr) {
	expr = unparen_expr(expr);

	TypeAndValue tv = type_and_value_of_expr(expr);
	Type *type = type_of_expr(expr);

	// Constant folding: if the expression has a known value, emit it directly
	if (tv.value.kind != ExactValue_Invalid && expr->kind != Ast_CompoundLit) {
		return fb_const_value(b, type, tv.value);
	}

	switch (expr->kind) {
	case Ast_Ident: {
		Entity *e = entity_of_node(expr);
		if (e != nullptr) {
			e = strip_entity_wrapping(e);
		}
		GB_ASSERT_MSG(e != nullptr, "%s in %.*s", expr_to_string(expr), LIT(b->entity->token.string));

		if (e->kind == Entity_Nil) {
			// Nil may have untyped nil type — use rawptr as a safe
			// pointer-sized zero regardless.
			Type *nil_type = (type != nullptr && is_type_typed(type)) ? type : t_rawptr;
			return fb_emit_iconst(b, nil_type, 0);
		}

		// Check variable map
		fbAddr *addr = map_get(&b->variable_map, e);
		if (addr != nullptr) {
			return fb_addr_load(b, *addr);
		}

		// Procedure reference
		if (e->kind == Entity_Procedure) {
			u32 *idx = map_get(&fb_entity_proc_map, e);
			if (idx != nullptr) {
				fbValue sym = fb_emit_symaddr(b, *idx);
				sym.type = type;
				return sym;
			}
		}

		// Global variable reference
		if (e->kind == Entity_Variable) {
			u32 *gidx = map_get(&b->module->global_entity_map, e);
			if (gidx != nullptr) {
				return fb_addr_load(b, fb_make_global_addr(b, e, *gidx));
			}
		}

		GB_PANIC("fb_build_expr Ident: unresolved entity '%.*s' (kind=%d) in proc '%.*s'",
		LIT(e->token.string), e->kind, LIT(b->entity->token.string));
		return fb_value_nil();
	}

	case Ast_BinaryExpr:
		return fb_build_binary_expr(b, expr);

	case Ast_UnaryExpr: {
		ast_node(ue, UnaryExpr, expr);
		if (ue->op.kind == Token_And) {
			Ast *ue_expr = unparen_expr(ue->expr);

			if (ue_expr->kind == Ast_TypeAssertion) {
				ast_node(ta, TypeAssertion, ue_expr);
				Type *assert_type = type_of_expr(ue_expr);
				i64 ptr_size = b->module->target.ptr_size;

				// Build the union expression and get its address.
				fbValue e = fb_build_expr(b, ta->expr);
				Type *union_type = e.type;
				// If the union value is already a pointer (aggregate convention), use it directly.
				// Otherwise, spill to a local to get an address.
				fbValue union_ptr;
				if (is_type_pointer(union_type)) {
					union_ptr = e;
					union_type = type_deref(union_type);
				} else {
					// Aggregate: e is tagged as the union type but is really a pointer.
					union_ptr = e;
					union_ptr.type = alloc_type_pointer(union_type);
				}
				Type *src_type = base_type(union_type);
				Type *dst_type = assert_type;

				if (is_type_tuple(tv.type)) {
					// ── Tuple return: x, ok := v.(T) → (^T, bool) ──
					Type *tuple = tv.type;
					Type *result_ptr_type = tuple->Tuple.variables[0]->type;
					Type *ok_type = tuple->Tuple.variables[1]->type;

					// Compare tag.
					fbValue ok;
					if (is_type_union_maybe_pointer(src_type)) {
						fbValue data = fb_emit_load(b, union_ptr, alloc_type_pointer(dst_type));
						fbValue nil_val = fb_emit_iconst(b, t_rawptr, 0);
						// Cast loaded pointer to rawptr for comparison.
						fbValue data_as_ptr = data;
						data_as_ptr.type = t_rawptr;
						ok = fb_emit_cmp(b, FB_CMP_NE, data_as_ptr, nil_val);
					} else {
						type_size_of(src_type); // ensure layout cached
						i64 tag_offset = src_type->Union.variant_block_size.load(std::memory_order_relaxed);
						Type *tag_type = union_tag_type(src_type);
						fbValue tag_ptr = fb_emit_member(b, union_ptr, tag_offset);
						fbValue src_tag = fb_emit_load(b, tag_ptr, tag_type);
						fbValue dst_tag = fb_emit_iconst(b, tag_type, union_variant_index(src_type, dst_type));
						ok = fb_emit_cmp(b, FB_CMP_EQ, src_tag, dst_tag);
					}

					// Result: allocate tuple, zero-init (nil ptr + false).
					fbAddr res = fb_add_local(b, tuple, nullptr, true);

					// Branch: ok → store ptr+true, else keep zero.
					u32 ok_block  = fb_new_block(b);
					u32 end_block = fb_new_block(b);
					fb_emit_branch(b, ok, ok_block, end_block);

					fb_set_block(b, ok_block);
					// Store data pointer (union_ptr rebranded as ^variant_type).
					fbValue data_ptr = union_ptr;
					data_ptr.type = result_ptr_type;
					fb_emit_store(b, res.base, data_ptr);
					// Store true at tuple offset ptr_size.
					fbValue ok_ptr = fb_emit_member(b, res.base, ptr_size);
					fbValue true_val = fb_emit_iconst(b, ok_type, 1);
					fb_emit_store(b, ok_ptr, true_val);
					fb_emit_jump(b, end_block);

					fb_set_block(b, end_block);
					// Return pointer to tuple (aggregate).
					fbValue result = res.base;
					result.type = tuple;
					return result;

				} else {
					// ── Direct return: x := v.(T) → ^T ──
					GB_ASSERT(is_type_pointer(tv.type));

					bool do_type_check = true;
					if (build_context.no_type_assert) {
						do_type_check = false;
					}
					// Check AST-level #no_type_assert flag.
					if ((expr->state_flags & StateFlag_no_type_assert) != 0) {
						do_type_check = false;
					}

					if (do_type_check) {
						fbValue ok;
						if (is_type_union_maybe_pointer(src_type)) {
							fbValue data = fb_emit_load(b, union_ptr, alloc_type_pointer(dst_type));
							fbValue nil_val = fb_emit_iconst(b, t_rawptr, 0);
							fbValue data_as_ptr = data;
							data_as_ptr.type = t_rawptr;
							ok = fb_emit_cmp(b, FB_CMP_NE, data_as_ptr, nil_val);
						} else {
							type_size_of(src_type);
							i64 tag_offset = src_type->Union.variant_block_size.load(std::memory_order_relaxed);
							Type *tag_type = union_tag_type(src_type);
							fbValue tag_ptr = fb_emit_member(b, union_ptr, tag_offset);
							fbValue src_tag = fb_emit_load(b, tag_ptr, tag_type);
							fbValue dst_tag = fb_emit_iconst(b, tag_type, union_variant_index(src_type, dst_type));
							ok = fb_emit_cmp(b, FB_CMP_EQ, src_tag, dst_tag);
						}

						u32 ok_block   = fb_new_block(b);
						u32 trap_block = fb_new_block(b);
						fb_emit_branch(b, ok, ok_block, trap_block);

						fb_set_block(b, trap_block);
						fb_inst_emit(b->proc, FB_TRAP, FB_VOID, FB_NOREG, FB_NOREG, FB_NOREG, 0, 0);
						fb_inst_emit(b->proc, FB_UNREACHABLE, FB_VOID, FB_NOREG, FB_NOREG, FB_NOREG, 0, 0);

						fb_set_block(b, ok_block);
					}

					fbValue data_ptr = union_ptr;
					data_ptr.type = tv.type;
					return data_ptr;
				}
			}

			fbAddr addr = fb_build_addr(b, ue->expr);
			fbValue ptr = addr.base;
			ptr.type = type;
			return ptr;
		}
		return fb_build_unary_expr(b, expr);
	}

	case Ast_TypeCast: {
		ast_node(tc, TypeCast, expr);
		fbValue e = fb_build_expr(b, tc->expr);
		return fb_emit_conv(b, e, type);
	}

	case Ast_AutoCast: {
		ast_node(ac, AutoCast, expr);
		fbValue val = fb_build_expr(b, ac->expr);
		return fb_emit_conv(b, val, type);
	}

	case Ast_CallExpr: {
		ast_node(ce, CallExpr, expr);

		TypeAndValue proc_tv = type_and_value_of_expr(ce->proc);

		// Type conversion via call syntax: int(x), f32(y), etc.
		if (proc_tv.mode == Addressing_Type) {
			GB_ASSERT(ce->args.count == 1);
			fbValue val = fb_build_expr(b, ce->args[0]);
			return fb_emit_conv(b, val, type);
		}

		// Built-in procedure: len(s), min(a,b), etc.
		if (proc_tv.mode == Addressing_Builtin) {
			Ast *proc_expr = unparen_expr(ce->proc);
			Entity *e = entity_of_node(proc_expr);
			BuiltinProcId id = BuiltinProc_Invalid;
			if (e != nullptr) {
				id = cast(BuiltinProcId)e->Builtin.id;
			} else {
				id = BuiltinProc_DIRECTIVE;
			}
			return fb_build_builtin_proc(b, expr, tv, id);
		}

		return fb_build_call_expr(b, expr);
	}

	case Ast_SelectorExpr:
	case Ast_IndexExpr:
	case Ast_DerefExpr:
	case Ast_SliceExpr:
		return fb_addr_load(b, fb_build_addr(b, expr));

	case Ast_Implicit:
		return fb_addr_load(b, fb_build_addr(b, expr));

	case Ast_Uninit: {
		u32 r = fb_inst_emit(b->proc, FB_UNDEF, fb_data_type(type), FB_NOREG, FB_NOREG, FB_NOREG, 0, 0);
		return fb_make_value(r, type);
	}

	case Ast_CompoundLit: {
		fbAddr addr = fb_build_compound_lit(b, expr);
		// For aggregate types, return the pointer to the temp.
		// Callers that assign to a variable will use memcpy.
		// For scalar types (shouldn't normally happen), load the value.
		fbType ft = fb_data_type(type);
		if (ft.kind != FBT_VOID) {
			return fb_addr_load(b, addr);
		}
		// Aggregate: return pointer, tagged with the aggregate type
		// so callers can distinguish scalar values from aggregate pointers.
		fbValue result = addr.base;
		result.type = type;
		return result;
	}

	case Ast_OrElseExpr: {
		ast_node(oe, OrElseExpr, expr);

		// Build the LHS: a multi-return (value, ok)
		fbValue last_val = fb_build_expr(b, oe->x);

		// Unpack: first return = value, last return = ok bool
		fbValue vals[2];
		fb_unpack_multi_return(b, last_val, vals, 2);
		fbValue value = vals[0];
		fbValue ok    = vals[1];

		// Result temp
		fbAddr result = fb_add_local(b, type, nullptr, false);

		u32 then_block = fb_new_block(b);
		u32 else_block = fb_new_block(b);
		u32 done_block = fb_new_block(b);

		fbValue ok_bool = fb_emit_conv(b, ok, t_bool);
		fb_emit_branch(b, ok_bool, then_block, else_block);

		// Then: ok == true, store value
		fb_set_block(b, then_block);
		fbValue conv_val = fb_emit_conv(b, value, type);
		fb_addr_store(b, result, conv_val);
		fb_emit_jump(b, done_block);

		// Else: ok == false, evaluate fallback
		fb_set_block(b, else_block);
		fbValue else_val = fb_build_expr(b, oe->y);
		fbValue else_conv = fb_emit_conv(b, else_val, type);
		fb_addr_store(b, result, else_conv);
		if (!fb_block_is_terminated(b)) {
			fb_emit_jump(b, done_block);
		}

		fb_set_block(b, done_block);
		return fb_addr_load(b, result);
	}

	case Ast_OrReturnExpr: {
		ast_node(ore, OrReturnExpr, expr);

		fbValue last_val = fb_build_expr(b, ore->expr);

		fbValue vals[2];
		fb_unpack_multi_return(b, last_val, vals, 2);
		fbValue value = vals[0];
		fbValue ok    = vals[1];

		u32 ok_block     = fb_new_block(b);
		u32 return_block = fb_new_block(b);

		fbValue ok_bool = fb_emit_conv(b, ok, t_bool);
		fb_emit_branch(b, ok_bool, ok_block, return_block);

		// Return block: ok == false, return the error value.
		// If the enclosing proc has split returns (multi-return), zero
		// the output pointers so callers see clean zero values.
		fb_set_block(b, return_block);
		if (b->proc->split_returns_index >= 0) {
			i32 split_count = b->proc->split_returns_count;
			Type *caller_pt = base_type(b->type);
			TypeTuple *caller_res = (caller_pt->Proc.results != nullptr)
				? &caller_pt->Proc.results->Tuple : nullptr;
			for (i32 i = 0; i < split_count; i++) {
				fbValue out_ptr = fb_load_split_return_ptr(b, i);
				Type *ret_type = caller_res->variables[i]->type;
				i64 size = type_size_of(ret_type);
				if (size > 0) {
					fb_emit_memzero(b, out_ptr, size, type_align_of(ret_type));
				}
			}
		}
		fb_emit_defer_stmts(b, fbDeferExit_Return, 0);
		fb_emit_ret(b, ok);

		// Ok block: return the value
		fb_set_block(b, ok_block);
		return fb_emit_conv(b, value, type);
	}

	case Ast_TernaryIfExpr: {
		ast_node(te, TernaryIfExpr, expr);
		GB_ASSERT(te->y != nullptr);

		fbType ft = fb_data_type(type);

		// Optimization: for scalar types with side-effect-free arms,
		// evaluate both and use SELECT (no control flow needed).
		if (ft.kind != FBT_VOID) {
			auto is_trivial = [](Ast *e) -> bool {
				e = unparen_expr(e);
				TypeAndValue tav = type_and_value_of_expr(e);
				if (tav.mode == Addressing_Constant) return true;
				if (e->kind == Ast_Ident) return true;
				if (e->kind == Ast_SelectorExpr) {
					Ast *operand = unparen_expr(e->SelectorExpr.expr);
					if (operand && operand->kind == Ast_Ident) return true;
				}
				if (e->kind == Ast_UnaryExpr && e->UnaryExpr.op.kind != Token_And) {
					Ast *operand = unparen_expr(e->UnaryExpr.expr);
					TypeAndValue otav = type_and_value_of_expr(operand);
					if (otav.mode == Addressing_Constant) return true;
					if (operand->kind == Ast_Ident) return true;
				}
				return false;
			};
			if (is_trivial(te->x) && is_trivial(te->y)) {
				fbValue cond = fb_build_expr(b, te->cond);
				cond = fb_emit_conv(b, cond, t_bool);
				fbValue x = fb_emit_conv(b, fb_build_expr(b, te->x), type);
				fbValue y = fb_emit_conv(b, fb_build_expr(b, te->y), type);
				return fb_emit_select(b, cond, x, y, type);
			}
		}

		// General path: branch into separate blocks, merge via temp alloca.
		fbAddr result = fb_add_local(b, type, nullptr, false);

		u32 then_block = fb_new_block(b);
		u32 else_block = fb_new_block(b);
		u32 done_block = fb_new_block(b);

		fbValue cond = fb_build_expr(b, te->cond);
		cond = fb_emit_conv(b, cond, t_bool);
		fb_emit_branch(b, cond, then_block, else_block);

		// Then: evaluate x, store to result
		fb_set_block(b, then_block);
		fbValue x_val = fb_build_expr(b, te->x);
		x_val = fb_emit_conv(b, x_val, type);
		if (ft.kind != FBT_VOID) {
			fb_addr_store(b, result, x_val);
		} else {
			fb_emit_copy_value(b, result.base, x_val, type);
		}
		if (!fb_block_is_terminated(b)) {
			fb_emit_jump(b, done_block);
		}

		// Else: evaluate y, store to result
		fb_set_block(b, else_block);
		fbValue y_val = fb_build_expr(b, te->y);
		y_val = fb_emit_conv(b, y_val, type);
		if (ft.kind != FBT_VOID) {
			fb_addr_store(b, result, y_val);
		} else {
			fb_emit_copy_value(b, result.base, y_val, type);
		}
		if (!fb_block_is_terminated(b)) {
			fb_emit_jump(b, done_block);
		}

		fb_set_block(b, done_block);
		if (ft.kind != FBT_VOID) {
			return fb_addr_load(b, result);
		}
		// Aggregate: return pointer tagged with aggregate type
		fbValue r = result.base;
		r.type = type;
		return r;
	}

	case Ast_TernaryWhenExpr: {
		ast_node(te, TernaryWhenExpr, expr);
		// Compile-time conditional: condition is a known bool constant.
		TypeAndValue cond_tv = type_and_value_of_expr(te->cond);
		GB_ASSERT(cond_tv.mode == Addressing_Constant);
		GB_ASSERT(cond_tv.value.kind == ExactValue_Bool);
		if (cond_tv.value.value_bool) {
			return fb_emit_conv(b, fb_build_expr(b, te->x), type);
		} else {
			return fb_emit_conv(b, fb_build_expr(b, te->y), type);
		}
	}

	case Ast_ImplicitSelectorExpr: {
		// .Field_Name in enum/union context — always a compile-time constant.
		TypeAndValue tav = type_and_value_of_expr(expr);
		GB_ASSERT_MSG(tav.mode == Addressing_Constant,
			"ImplicitSelectorExpr expected Addressing_Constant, got %d", tav.mode);
		return fb_const_value(b, type, tav.value);
	}

	case Ast_SelectorCallExpr: {
		ast_node(se, SelectorCallExpr, expr);
		// The checker has already rewritten obj.method(args) into a regular call.
		GB_ASSERT(se->modified_call);
		return fb_build_expr(b, se->call);
	}

	case Ast_TypeAssertion: {
		ast_node(ta, TypeAssertion, expr);

		fbValue e = fb_build_expr(b, ta->expr);
		Type *union_type = e.type;

		// Get the union pointer. Aggregates (unions) are passed as pointers
		// tagged with the aggregate type in the fast backend.
		fbValue union_ptr = e;
		union_ptr.type = alloc_type_pointer(union_type);
		Type *src_type = base_type(union_type);

		bool is_tuple = is_type_tuple(type);
		Type *tuple = type;
		if (!is_tuple) {
			tuple = make_optional_ok_type(type);
		}
		Type *dst_type = tuple->Tuple.variables[0]->type;
		Type *ok_type  = tuple->Tuple.variables[1]->type;

		// Allocate result tuple, zero-init (zeroed value + false).
		fbAddr res = fb_add_local(b, tuple, nullptr, true);

		// Check no_type_assert for direct (non-tuple) assertions.
		bool do_type_check = true;
		if (!is_tuple) {
			if (build_context.no_type_assert) {
				do_type_check = false;
			}
			if ((expr->state_flags & StateFlag_no_type_assert) != 0) {
				do_type_check = false;
			}
			if (!do_type_check) {
				// No check: just load the data and return it.
				fbValue data_ptr = union_ptr;
				data_ptr.type = alloc_type_pointer(dst_type);
				fbType dst_ft = fb_data_type(dst_type);
				if (dst_ft.kind != FBT_VOID) {
					return fb_emit_load(b, data_ptr, dst_type);
				} else {
					fbValue r = data_ptr;
					r.type = dst_type;
					return r;
				}
			}
		}

		// Compare tag to determine if the variant matches.
		fbValue cond;
		if (is_type_union_maybe_pointer(src_type)) {
			// Maybe-pointer union: compare data against nil.
			fbValue data = fb_emit_load(b, union_ptr, dst_type);
			fbValue nil_val = fb_emit_iconst(b, t_rawptr, 0);
			fbValue data_as_ptr = data;
			data_as_ptr.type = t_rawptr;
			cond = fb_emit_cmp(b, FB_CMP_NE, data_as_ptr, nil_val);
		} else {
			type_size_of(src_type); // ensure layout cached
			i64 tag_offset = src_type->Union.variant_block_size.load(std::memory_order_relaxed);
			Type *tag_type = union_tag_type(src_type);
			fbValue tag_ptr = fb_emit_member(b, union_ptr, tag_offset);
			fbValue src_tag = fb_emit_load(b, tag_ptr, tag_type);
			fbValue dst_tag = fb_emit_iconst(b, tag_type, union_variant_index(src_type, dst_type));
			cond = fb_emit_cmp(b, FB_CMP_EQ, src_tag, dst_tag);
		}

		u32 ok_block  = fb_new_block(b);
		u32 end_block = fb_new_block(b);
		fb_emit_branch(b, cond, ok_block, end_block);

		fb_set_block(b, ok_block);
		{
			// Load variant data from the union and store into result tuple[0].
			fbValue data_ptr = union_ptr;
			data_ptr.type = alloc_type_pointer(dst_type);
			fbType dst_ft = fb_data_type(dst_type);
			if (dst_ft.kind != FBT_VOID) {
				fbValue data = fb_emit_load(b, data_ptr, dst_type);
				fb_emit_store(b, res.base, data);
			} else {
				i64 data_size = type_size_of(dst_type);
				if (data_size > 0) {
					fbValue sz = fb_emit_iconst(b, t_int, data_size);
					fb_emit_memcpy(b, res.base, data_ptr, sz, type_align_of(dst_type));
				}
			}
			// Store true into ok field.
			i64 ok_offset = type_offset_of(tuple, 1);
			fbValue ok_ptr = fb_emit_member(b, res.base, ok_offset);
			fb_emit_store(b, ok_ptr, fb_emit_iconst(b, ok_type, 1));
		}
		fb_emit_jump(b, end_block);

		fb_set_block(b, end_block);

		if (!is_tuple) {
			// Direct assertion: check ok, trap on failure, return value.
			i64 ok_offset = type_offset_of(tuple, 1);
			fbValue ok_ptr = fb_emit_member(b, res.base, ok_offset);
			fbValue ok_val = fb_emit_load(b, ok_ptr, ok_type);

			u32 pass_block = fb_new_block(b);
			u32 trap_block = fb_new_block(b);
			fb_emit_branch(b, ok_val, pass_block, trap_block);

			fb_set_block(b, trap_block);
			fb_inst_emit(b->proc, FB_TRAP, FB_VOID, FB_NOREG, FB_NOREG, FB_NOREG, 0, 0);
			fb_inst_emit(b->proc, FB_UNREACHABLE, FB_VOID, FB_NOREG, FB_NOREG, FB_NOREG, 0, 0);

			fb_set_block(b, pass_block);
			// Load and return the value.
			fbType dst_ft = fb_data_type(dst_type);
			if (dst_ft.kind != FBT_VOID) {
				return fb_emit_load(b, res.base, dst_type);
			} else {
				fbValue r = res.base;
				r.type = dst_type;
				return r;
			}
		}

		// Tuple: return as aggregate pointer.
		fbValue result = res.base;
		result.type = tuple;
		return result;
	}

	default:
		GB_PANIC("TODO fb_build_expr %.*s", LIT(ast_strings[expr->kind]));
		break;
	}

	return fb_value_nil();
}

// ───────────────────────────────────────────────────────────────────────
// Step 5: Statement builder
// ───────────────────────────────────────────────────────────────────────

gb_internal void fb_scope_open(fbBuilder *b, Scope *scope) {
	b->scope_index += 1;
	array_add(&b->scope_stack, scope);
}

// Emit a single deferred statement inline at the current insertion point.
gb_internal void fb_build_defer_stmt(fbBuilder *b, fbDefer const &d) {
	if (fb_block_is_terminated(b)) return;
	if (d.kind == fbDefer_Node) {
		fb_build_stmt(b, d.stmt);
	}
	// fbDefer_Proc: deferred procedure calls not yet implemented
}

// Emit deferred statements according to the exit kind.
//
// Default: LIFO execution of defers in the current scope only, popped after emission.
// Return:  LIFO execution of ALL defers (all scopes), not popped (stack unwinds naturally).
// Branch:  LIFO execution of defers whose scope_index > target scope, not popped.
gb_internal void fb_emit_defer_stmts(fbBuilder *b, fbDeferExitKind kind, i32 target_scope_index) {
	isize i = b->defer_stack.count;
	while (i-- > 0) {
		fbDefer const &d = b->defer_stack[i];

		switch (kind) {
		case fbDeferExit_Default:
			if (d.scope_index == b->scope_index && d.scope_index > 0) {
				fb_build_defer_stmt(b, d);
				array_pop(&b->defer_stack);
				continue;
			}
			return; // stop at first non-matching scope
		case fbDeferExit_Return:
			fb_build_defer_stmt(b, d);
			break;
		case fbDeferExit_Branch:
			if (target_scope_index < d.scope_index) {
				fb_build_defer_stmt(b, d);
			}
			break;
		}
	}
}

gb_internal void fb_scope_close(fbBuilder *b, fbDeferExitKind kind, i32 target_scope_index) {
	fb_emit_defer_stmts(b, kind, target_scope_index);
	GB_ASSERT(b->scope_index > 0);
	b->scope_index -= 1;
	array_pop(&b->scope_stack);
}

gb_internal void fb_build_constant_value_decl(fbBuilder *b, AstValueDecl *vd) {
	if (vd == nullptr || vd->is_mutable) {
		return;
	}
	// In Phase 6a, nested procedure declarations are not handled.
	// They would require creating child fbProcs and adding them to the module.
}

gb_internal void fb_build_stmt_list(fbBuilder *b, Slice<Ast *> const &stmts) {
	// First pass: constant value declarations (nested procs)
	for (Ast *stmt : stmts) {
		if (stmt->kind == Ast_ValueDecl) {
			fb_build_constant_value_decl(b, &stmt->ValueDecl);
		}
	}
	// Second pass: all statements
	for (Ast *stmt : stmts) {
		fb_build_stmt(b, stmt);
	}
}

gb_internal void fb_build_mutable_value_decl(fbBuilder *b, Ast *node) {
	ast_node(vd, ValueDecl, node);
	if (!vd->is_mutable) {
		return;
	}

	i32 name_count = cast(i32)vd->names.count;
	i32 value_count = cast(i32)vd->values.count;

	// Multi-return: single RHS call producing multiple values
	if (value_count == 1 && name_count > 1) {
		Type *rhs_type = type_of_expr(vd->values[0]);
		if (rhs_type != nullptr && rhs_type->kind == Type_Tuple) {
			fbValue last_val = fb_build_expr(b, vd->values[0]);

			auto vals = array_make<fbValue>(heap_allocator(), name_count, name_count);

			// Determine unpack method: if split return temps were set up
			// (procedure call), use them. Otherwise the result is an
			// aggregate tuple pointer — load fields directly.
			if (b->last_call_split_count > 0 || b->last_call_split_temps != nullptr) {
				fb_unpack_multi_return(b, last_val, vals.data, name_count);
			} else {
				// Aggregate tuple: last_val is a pointer to the tuple memory.
				fbValue tuple_ptr = last_val;
				tuple_ptr.type = alloc_type_pointer(rhs_type);
				for (i32 i = 0; i < name_count; i++) {
					Type *field_type = rhs_type->Tuple.variables[i]->type;
					i64 offset = type_offset_of(rhs_type, i);
					fbType ft = fb_data_type(field_type);
					if (ft.kind != FBT_VOID) {
						// Scalar: load the field value.
						vals[i] = fb_load_field(b, tuple_ptr, offset, field_type);
					} else {
						// Aggregate: return pointer to field (don't load).
						// Fast backend convention: aggregate values are pointers
						// tagged with the aggregate type.
						fbValue field_ptr = tuple_ptr;
						if (offset != 0) {
							field_ptr = fb_emit_member(b, tuple_ptr, offset);
						}
						field_ptr.type = field_type;
						vals[i] = field_ptr;
					}
				}
			}

			// Create locals and assign
			for_array(i, vd->names) {
				Ast *name = vd->names[i];
				if (is_blank_ident(name)) continue;
				Entity *e = entity_of_node(name);
				if (e == nullptr) continue;

				fbAddr local = fb_add_local(b, e->type, e, true);
				if (i < vals.count) {
					fbValue val = fb_emit_conv(b, vals[i], e->type);
					fbType ft = fb_data_type(e->type);
					if (ft.kind != FBT_VOID) {
						fb_addr_store(b, local, val);
					} else {
						fb_emit_copy_value(b, local.base, val, e->type);
					}
				}
			}
			array_free(&vals);
			return;
		}
	}

	// Normal path: build RHS values 1:1 with LHS names
	auto inits = array_make<fbValue>(heap_allocator(), 0, vd->values.count);
	for (Ast *rhs : vd->values) {
		fbValue init = fb_build_expr(b, rhs);
		array_add(&inits, init);
	}

	// Create locals and store initial values
	for_array(i, vd->names) {
		Ast *name = vd->names[i];
		if (is_blank_ident(name)) continue;

		Entity *e = entity_of_node(name);
		if (e == nullptr) continue;

		bool zero_init = (vd->values.count == 0);
		fbAddr local = fb_add_local(b, e->type, e, zero_init);

		if (i < inits.count) {
			fbValue init = inits[i];
			init = fb_emit_conv(b, init, e->type);
			fbType local_ft = fb_data_type(e->type);
			if (local_ft.kind != FBT_VOID) {
				// Scalar: store
				fb_addr_store(b, local, init);
			} else {
				// Aggregate: init is a pointer to data, memcpy
				fb_emit_copy_value(b, local.base, init, e->type);
			}
		}
	}

	array_free(&inits);
}

gb_internal void fb_build_return_stmt(fbBuilder *b, Slice<Ast *> const &results) {
	Type *pt = base_type(b->type);
	GB_ASSERT(pt->kind == Type_Proc);
	TypeProc *proc_type = &pt->Proc;
	bool is_odin_cc = (proc_type->calling_convention == ProcCC_Odin);

	TypeTuple *res_tuple = (proc_type->results != nullptr)
		? &proc_type->results->Tuple : nullptr;
	i32 res_count = res_tuple ? cast(i32)res_tuple->variables.count : 0;

	if (results.count == 0) {
		// Bare `return` — for named results, store them through split return
		// pointers.  Implicit named-result returns are handled later.
		fb_emit_defer_stmts(b, fbDeferExit_Return, 0);
		fb_emit_ret_void(b);
		return;
	}

	if (results.count == 1 && !(is_odin_cc && res_count > 1)) {
		// Single return value (the common case)
		fbValue val = fb_build_expr(b, results[0]);
		Type *ret_type = nullptr;
		if (is_odin_cc && res_count > 0) {
			ret_type = res_tuple->variables[res_count - 1]->type;
		} else if (res_count > 0) {
			ret_type = res_tuple->variables[0]->type;
		}
		if (ret_type != nullptr) {
			val = fb_emit_conv(b, val, ret_type);
		}
		fb_emit_defer_stmts(b, fbDeferExit_Return, 0);
		fb_emit_ret(b, val);
		return;
	}

	// Multi-return (Odin CC): store first N-1 values through hidden output
	// pointer params, return the last value in a register.
	GB_ASSERT(is_odin_cc && res_count > 1);
	GB_ASSERT(b->proc->split_returns_index >= 0);

	// Phase 1: Flatten — build each result expression. If a single
	// expression produces a tuple (return-forwarding of a multi-return
	// call), unpack it into individual values.
	auto flat_vals = array_make<fbValue>(heap_allocator(), 0, res_count);
	for (i32 i = 0; i < cast(i32)results.count; i++) {
		Ast *rexpr = results[i];
		Type *rtype = type_of_expr(rexpr);
		fbValue val = fb_build_expr(b, rexpr);

		if (rtype != nullptr && rtype->kind == Type_Tuple) {
			i32 tuple_count = cast(i32)rtype->Tuple.variables.count;
			auto unpacked = array_make<fbValue>(heap_allocator(), tuple_count, tuple_count);
			fb_unpack_multi_return(b, val, unpacked.data, tuple_count);
			for (i32 j = 0; j < tuple_count; j++) {
				array_add(&flat_vals, unpacked[j]);
			}
			array_free(&unpacked);
		} else {
			array_add(&flat_vals, val);
		}
	}

	// Phase 2: Store first N-1 values through split return output pointers,
	// return the last value in a register.
	for (i32 i = 0; i < res_count - 1 && i < cast(i32)flat_vals.count; i++) {
		fbValue val = flat_vals[i];
		Type *ret_type = res_tuple->variables[i]->type;
		fbType ret_ft = fb_data_type(ret_type);

		// Convert value to the expected return type.
		// Skip conversion for aggregates (FBT_VOID) — val is already a
		// pointer to the data and fb_emit_conv can't handle that.
		if (ret_ft.kind != FBT_VOID) {
			val = fb_emit_conv(b, val, ret_type);
		}

		// Load the hidden output pointer from the split return param slot
		fbValue out_ptr = fb_load_split_return_ptr(b, i);

		// Store value through the output pointer
		fb_emit_copy_value(b, out_ptr, val, ret_type);
	}

	// Build and return the last value
	fbValue last_val = (cast(i32)flat_vals.count >= res_count)
		? flat_vals[res_count - 1]
		: fb_build_expr(b, results[res_count - 1]);
	array_free(&flat_vals);

	Type *last_type = res_tuple->variables[res_count - 1]->type;
	last_val = fb_emit_conv(b, last_val, last_type);

	fb_emit_defer_stmts(b, fbDeferExit_Return, 0);

	fbType last_ft = fb_data_type(last_type);
	if (last_ft.kind != FBT_VOID) {
		fb_emit_ret(b, last_val);
	} else {
		// Aggregate last return: would need sret (not yet implemented)
		GB_PANIC("fast backend: aggregate last return value not yet supported (needs sret)");
	}
}

gb_internal void fb_build_assign_stmt(fbBuilder *b, AstAssignStmt *as) {
	if (as->op.kind == Token_Eq) {
		i32 lhs_count = cast(i32)as->lhs.count;
		i32 rhs_count = cast(i32)as->rhs.count;

		// Multi-return: single RHS call producing multiple values
		if (rhs_count == 1 && lhs_count > 1) {
			Type *rhs_type = type_of_expr(as->rhs[0]);
			if (rhs_type != nullptr && rhs_type->kind == Type_Tuple) {
				fbValue last_val = fb_build_expr(b, as->rhs[0]);
				auto vals = array_make<fbValue>(heap_allocator(), lhs_count, lhs_count);

				if (b->last_call_split_count > 0 || b->last_call_split_temps != nullptr) {
					fb_unpack_multi_return(b, last_val, vals.data, lhs_count);
				} else {
					fbValue tuple_ptr = last_val;
					tuple_ptr.type = alloc_type_pointer(rhs_type);
					for (i32 i = 0; i < lhs_count; i++) {
						Type *field_type = rhs_type->Tuple.variables[i]->type;
						i64 offset = type_offset_of(rhs_type, i);
						vals[i] = fb_load_field(b, tuple_ptr, offset, field_type);
					}
				}

				for_array(i, as->lhs) {
					Ast *lhs_expr = as->lhs[i];
					if (is_blank_ident(lhs_expr)) continue;
					if (i >= vals.count) break;

					fbAddr addr = fb_build_addr(b, lhs_expr);
					fbValue val = fb_emit_conv(b, vals[i], addr.type);
					fbType addr_ft = fb_data_type(addr.type);
					if (addr_ft.kind != FBT_VOID) {
						fb_addr_store(b, addr, val);
					} else {
						fb_emit_copy_value(b, addr.base, val, addr.type);
					}
				}
				array_free(&vals);
				return;
			}
		}

		// Normal path: 1:1 RHS-to-LHS
		auto rhs_vals = array_make<fbValue>(heap_allocator(), 0, as->rhs.count);
		for (Ast *rhs : as->rhs) {
			fbValue val = fb_build_expr(b, rhs);
			array_add(&rhs_vals, val);
		}

		for_array(i, as->lhs) {
			Ast *lhs_expr = as->lhs[i];
			if (is_blank_ident(lhs_expr)) continue;
			if (i >= rhs_vals.count) break;

			fbAddr addr = fb_build_addr(b, lhs_expr);
			fbValue val = fb_emit_conv(b, rhs_vals[i], addr.type);
			fbType addr_ft = fb_data_type(addr.type);
			if (addr_ft.kind != FBT_VOID) {
				// Scalar: store
				fb_addr_store(b, addr, val);
			} else {
				// Aggregate: memcpy
				fb_emit_copy_value(b, addr.base, val, addr.type);
			}
		}

		array_free(&rhs_vals);
	} else {
		// Compound assignment (+=, -=, etc.)
		GB_ASSERT(as->lhs.count == 1 && as->rhs.count == 1);

		fbAddr addr = fb_build_addr(b, as->lhs[0]);
		fbValue old_val = fb_addr_load(b, addr);
		fbValue rhs = fb_build_expr(b, as->rhs[0]);

		fbOp op;
		Type *type = addr.type;
		bool is_float = fb_type_is_float(fb_data_type(type));
		switch (as->op.kind) {
		case Token_AddEq: op = is_float ? FB_FADD : FB_ADD; break;
		case Token_SubEq: op = is_float ? FB_FSUB : FB_SUB; break;
		case Token_MulEq: op = is_float ? FB_FMUL : FB_MUL; break;
		case Token_QuoEq:
			op = is_float ? FB_FDIV : (fb_type_is_signed(type) ? FB_SDIV : FB_UDIV);
			break;
		case Token_ModEq: op = fb_type_is_signed(type) ? FB_SMOD : FB_UMOD; break;
		case Token_AndEq: op = FB_AND; break;
		case Token_OrEq:  op = FB_OR;  break;
		case Token_XorEq: op = FB_XOR; break;
		case Token_ShlEq: op = FB_SHL; break;
		case Token_ShrEq: op = fb_type_is_signed(type) ? FB_ASHR : FB_LSHR; break;
		case Token_AndNotEq: {
			fbType ft = fb_data_type(type);
			if (ft.kind == FBT_VOID) ft = FB_I64;
			u32 not_r = fb_inst_emit(b->proc, FB_NOT, ft, rhs.id, FB_NOREG, FB_NOREG, 0, 0);
			fbValue result = fb_emit_arith(b, FB_AND, old_val, fb_make_value(not_r, type), type);
			fb_addr_store(b, addr, result);
			return;
		}
		default:
			GB_PANIC("TODO fb_build_assign_stmt op=%d", as->op.kind);
			return;
		}

		rhs = fb_emit_conv(b, rhs, type);
		fbValue result = fb_emit_arith(b, op, old_val, rhs, type);
		fb_addr_store(b, addr, result);
	}
}

gb_internal void fb_build_if_stmt(fbBuilder *b, Ast *node) {
	ast_node(is, IfStmt, node);

	fb_scope_open(b, is->scope);

	if (is->init != nullptr) {
		fb_build_stmt(b, is->init);
	}

	u32 then_block = fb_new_block(b);
	u32 done_block = fb_new_block(b);
	u32 else_block = done_block;
	if (is->else_stmt != nullptr) {
		else_block = fb_new_block(b);
	}

	// Build condition
	fbValue cond = fb_build_expr(b, is->cond);
	fbValue cond_bool = fb_emit_conv(b, cond, t_bool);
	fb_emit_branch(b, cond_bool, then_block, else_block);

	// Then block
	fb_set_block(b, then_block);
	fb_build_stmt(b, is->body);
	if (!fb_block_is_terminated(b)) {
		fb_emit_jump(b, done_block);
	}

	// Else block
	if (is->else_stmt != nullptr) {
		fb_set_block(b, else_block);
		fb_build_stmt(b, is->else_stmt);
		if (!fb_block_is_terminated(b)) {
			fb_emit_jump(b, done_block);
		}
	}

	fb_set_block(b, done_block);
	fb_scope_close(b, fbDeferExit_Default, 0);
}

// ───── Range statement helpers ─────

// Strip unary & prefix from range variable identifier.
gb_internal Ast *fb_strip_and_prefix(Ast *ident) {
	if (ident != nullptr && ident->kind == Ast_UnaryExpr &&
	    ident->UnaryExpr.op.kind == Token_And) {
		ident = ident->UnaryExpr.expr;
	}
	return ident;
}

// Integer range interval: for val, idx in lo..<hi  /  lo..=hi  /  lo..hi
gb_internal void fb_build_range_interval(fbBuilder *b, AstBinaryExpr *node,
                                          AstRangeStmt *rs, Scope *scope) {
	fb_scope_open(b, scope);

	Ast *val0 = rs->vals.count > 0 ? fb_strip_and_prefix(rs->vals[0]) : nullptr;
	Ast *val1 = rs->vals.count > 1 ? fb_strip_and_prefix(rs->vals[1]) : nullptr;
	Type *val0_type = nullptr;
	Type *val1_type = nullptr;
	if (val0 != nullptr && !is_blank_ident(val0)) {
		val0_type = type_of_expr(val0);
	}
	if (val1 != nullptr && !is_blank_ident(val1)) {
		val1_type = type_of_expr(val1);
	}

	// Determine comparison: < for ..<, <= for ..= and ..
	bool inclusive = (node->op.kind != Token_RangeHalf);

	// Evaluate lower bound and create the iteration variable.
	fbValue lower = fb_build_expr(b, node->left);
	Type *iter_type = val0_type ? val0_type : lower.type;

	fbAddr value = fb_add_local(b, iter_type,
		val0_type ? entity_of_node(val0) : nullptr, false);
	fb_addr_store(b, value, lower);

	// Optional index variable (second binding).
	fbAddr index = {};
	bool has_index = (val1_type != nullptr);
	if (has_index) {
		index = fb_add_local(b, val1_type, entity_of_node(val1), false);
		fb_addr_store(b, index, fb_emit_iconst(b, val1_type, 0));
	}

	// Store upper bound in a local so it survives across blocks.
	fbAddr upper_addr = fb_add_local(b, iter_type, nullptr, false);

	u32 loop_block = fb_new_block(b);
	u32 body_block = fb_new_block(b);
	u32 post_block = fb_new_block(b);
	u32 done_block = fb_new_block(b);

	// For inclusive ranges, add an extra wrapping check block between
	// body and post to avoid infinite loops when upper == type max.
	u32 check_block = FB_NOREG;
	if (inclusive) {
		check_block = fb_new_block(b);
	}

	// Register label targets for break/continue.
	u32 continue_target = inclusive ? check_block : post_block;
	if (rs->label != nullptr) {
		for_array(i, b->branch_regions) {
			if (b->branch_regions[i].cond == rs->label) {
				b->branch_regions[i].false_block = done_block;     // break
				b->branch_regions[i].true_block  = continue_target; // continue
				break;
			}
		}
	}

	// Jump to loop header.
	fb_emit_jump(b, loop_block);
	fb_set_block(b, loop_block);

	// Evaluate upper bound once per iteration and store.
	fbValue upper = fb_build_expr(b, node->right);
	fb_addr_store(b, upper_addr, upper);

	// Condition: curr </<= upper.
	fbValue curr = fb_addr_load(b, value);

	bool is_signed = is_type_integer(iter_type) &&
	                 !is_type_unsigned(iter_type);
	fbOp cmp_op;
	if (is_type_float(iter_type)) {
		cmp_op = inclusive ? FB_CMP_FLE : FB_CMP_FLT;
	} else {
		if (inclusive) {
			cmp_op = is_signed ? FB_CMP_SLE : FB_CMP_ULE;
		} else {
			cmp_op = is_signed ? FB_CMP_SLT : FB_CMP_ULT;
		}
	}
	fbValue cond = fb_emit_cmp(b, cmp_op, curr, upper);
	fb_emit_branch(b, cond, body_block, done_block);

	// Body.
	fb_set_block(b, body_block);

	// Push break/continue targets.
	fbTargetList tl = {};
	tl.prev = b->target_list;
	tl.break_block = done_block;
	tl.continue_block = continue_target;
	tl.scope_index = b->scope_index;
	tl.is_block = false;
	b->target_list = &tl;

	fb_build_stmt(b, rs->body);

	b->target_list = tl.prev;

	// Fall through to post (or wrapping check for inclusive).
	if (!fb_block_is_terminated(b)) {
		fb_emit_jump(b, continue_target);
	}

	// Wrapping check for inclusive ranges: if curr == upper, we already
	// processed the last value, so exit without incrementing (which would wrap).
	// Reload both values from locals (they may not survive the body in registers).
	if (inclusive) {
		fb_set_block(b, check_block);
		fbValue curr_reload = fb_addr_load(b, value);
		fbValue upper_reload = fb_addr_load(b, upper_addr);
		fbOp ne_op = is_type_float(iter_type) ? FB_CMP_FNE : FB_CMP_NE;
		fbValue wrap_cond = fb_emit_cmp(b, ne_op, curr_reload, upper_reload);
		fb_emit_branch(b, wrap_cond, post_block, done_block);
	}

	// Post: increment value and index, loop back.
	fb_set_block(b, post_block);
	fbValue v = fb_addr_load(b, value);
	fbValue one = is_type_float(iter_type)
		? fb_emit_fconst(b, iter_type, 1.0)
		: fb_emit_iconst(b, iter_type, 1);
	fbOp add_op = is_type_float(iter_type) ? FB_FADD : FB_ADD;
	fbValue v_next = fb_emit_arith(b, add_op, v, one, iter_type);
	fb_addr_store(b, value, v_next);

	if (has_index) {
		fbValue i_val = fb_addr_load(b, index);
		fbValue i_next = fb_emit_arith(b, FB_ADD, i_val,
			fb_emit_iconst(b, val1_type, 1), val1_type);
		fb_addr_store(b, index, i_next);
	}
	fb_emit_jump(b, loop_block);

	fb_set_block(b, done_block);
	fb_scope_close(b, fbDeferExit_Default, 0);
}

// Indexed range: for val, idx in array / slice / dynamic_array
gb_internal void fb_build_range_indexed(fbBuilder *b, AstRangeStmt *rs,
                                         Scope *scope) {
	fb_scope_open(b, scope);

	Ast *expr = unparen_expr(rs->expr);
	Type *expr_type = type_of_expr(expr);
	Type *et = base_type(type_deref(expr_type));

	Ast *val0 = rs->vals.count > 0 ? fb_strip_and_prefix(rs->vals[0]) : nullptr;
	Ast *val1 = rs->vals.count > 1 ? fb_strip_and_prefix(rs->vals[1]) : nullptr;
	Type *val0_type = nullptr;
	Type *val1_type = nullptr;
	if (val0 != nullptr && !is_blank_ident(val0)) {
		val0_type = type_of_expr(val0);
	}
	if (val1 != nullptr && !is_blank_ident(val1)) {
		val1_type = type_of_expr(val1);
	}

	// Resolve the collection address and determine count + data pointer.
	fbAddr base_addr = fb_build_addr(b, expr);
	fbValue data_ptr = base_addr.base;
	fbValue count = {};
	Type *elem_type = nullptr;
	i64 stride = 0;

	switch (et->kind) {
	case Type_Array:
		elem_type = et->Array.elem;
		stride = type_size_of(elem_type);
		count = fb_emit_iconst(b, t_int, et->Array.count);
		break;
	case Type_Slice:
		elem_type = et->Slice.elem;
		stride = type_size_of(elem_type);
		// Slice layout: {data rawptr, len int}
		count = fb_emit_load(b, fb_emit_member(b, base_addr.base, build_context.ptr_size), t_int);
		data_ptr = fb_emit_load(b, base_addr.base, t_rawptr);
		break;
	case Type_DynamicArray:
		elem_type = et->DynamicArray.elem;
		stride = type_size_of(elem_type);
		// Dynamic array layout: {data rawptr, len int, cap int, allocator ...}
		count = fb_emit_load(b, fb_emit_member(b, base_addr.base, build_context.ptr_size), t_int);
		data_ptr = fb_emit_load(b, base_addr.base, t_rawptr);
		break;
	default:
		GB_PANIC("fb_build_range_indexed: unsupported type %s", type_to_string(expr_type));
		return;
	}

	// Create index variable (internal, always needed for element access).
	fbAddr index_addr = fb_add_local(b, t_int, nullptr, false);

	bool is_reverse = rs->reverse;

	u32 loop_block = fb_new_block(b);
	u32 body_block = fb_new_block(b);
	u32 done_block = fb_new_block(b);

	// Register label targets.
	if (rs->label != nullptr) {
		for_array(i, b->branch_regions) {
			if (b->branch_regions[i].cond == rs->label) {
				b->branch_regions[i].false_block = done_block; // break
				b->branch_regions[i].true_block  = loop_block; // continue
				break;
			}
		}
	}

	if (!is_reverse) {
		// Forward: index starts at -1, increments at top of loop.
		fb_addr_store(b, index_addr, fb_emit_iconst(b, t_int, -1));
		fb_emit_jump(b, loop_block);
		fb_set_block(b, loop_block);

		fbValue idx = fb_addr_load(b, index_addr);
		fbValue one = fb_emit_iconst(b, t_int, 1);
		fbValue next_idx = fb_emit_arith(b, FB_ADD, idx, one, t_int);
		fb_addr_store(b, index_addr, next_idx);

		fbValue cond = fb_emit_cmp(b, FB_CMP_SLT, next_idx, count);
		fb_emit_branch(b, cond, body_block, done_block);
	} else {
		// Reverse: index starts at count, decrements at top of loop.
		fb_addr_store(b, index_addr, count);
		fb_emit_jump(b, loop_block);
		fb_set_block(b, loop_block);

		fbValue idx = fb_addr_load(b, index_addr);
		fbValue one = fb_emit_iconst(b, t_int, 1);
		fbValue next_idx = fb_emit_arith(b, FB_SUB, idx, one, t_int);
		fb_addr_store(b, index_addr, next_idx);

		fbValue zero = fb_emit_iconst(b, t_int, 0);
		fbValue cond = fb_emit_cmp(b, FB_CMP_SLT, next_idx, zero);
		fb_emit_branch(b, cond, done_block, body_block);
	}

	// Body.
	fb_set_block(b, body_block);

	fbValue cur_idx = fb_addr_load(b, index_addr);

	// Bind val0 (element value).
	if (val0_type != nullptr) {
		Entity *e0 = entity_of_node(val0);
		fbValue elem_ptr = fb_emit_array_access(b, data_ptr, cur_idx, stride);
		fbAddr val0_addr = fb_add_local(b, val0_type, e0, false);
		fbValue elem_val = fb_emit_load(b, elem_ptr, elem_type);
		if (val0_type != elem_type) {
			elem_val = fb_emit_conv(b, elem_val, val0_type);
		}
		fb_addr_store(b, val0_addr, elem_val);
	}

	// Bind val1 (index).
	if (val1_type != nullptr) {
		Entity *e1 = entity_of_node(val1);
		fbAddr val1_addr = fb_add_local(b, val1_type, e1, false);
		fbValue idx_val = cur_idx;
		if (val1_type != t_int) {
			idx_val = fb_emit_conv(b, cur_idx, val1_type);
		}
		fb_addr_store(b, val1_addr, idx_val);
	}

	// Push break/continue targets.
	fbTargetList tl = {};
	tl.prev = b->target_list;
	tl.break_block = done_block;
	tl.continue_block = loop_block;
	tl.scope_index = b->scope_index;
	tl.is_block = false;
	b->target_list = &tl;

	fb_build_stmt(b, rs->body);

	b->target_list = tl.prev;

	if (!fb_block_is_terminated(b)) {
		fb_emit_jump(b, loop_block);
	}

	fb_set_block(b, done_block);
	fb_scope_close(b, fbDeferExit_Default, 0);
}

// Main range statement dispatch.
gb_internal void fb_build_range_stmt(fbBuilder *b, Ast *node) {
	ast_node(rs, RangeStmt, node);
	Ast *expr = unparen_expr(rs->expr);

	// Integer/float range interval: for x in lo..<hi
	if (is_ast_range(expr)) {
		fb_build_range_interval(b, &expr->BinaryExpr, rs, rs->scope);
		return;
	}

	// Collection-based iteration.
	Type *expr_type = type_of_expr(expr);
	Type *et = base_type(type_deref(expr_type));

	switch (et->kind) {
	case Type_Array:
	case Type_Slice:
	case Type_DynamicArray:
		fb_build_range_indexed(b, rs, rs->scope);
		return;
	default:
		break;
	}

	GB_PANIC("TODO fb_build_range_stmt for %s", type_to_string(expr_type));
}

gb_internal void fb_build_for_stmt(fbBuilder *b, Ast *node) {
	ast_node(fs, ForStmt, node);

	fb_scope_open(b, fs->scope);

	if (fs->init != nullptr) {
		fb_build_stmt(b, fs->init);
	}

	u32 body_block = fb_new_block(b);
	u32 done_block = fb_new_block(b);
	u32 loop_block = body_block;
	if (fs->cond != nullptr) {
		loop_block = fb_new_block(b);
	}
	u32 post_block = loop_block;
	if (fs->post != nullptr) {
		post_block = fb_new_block(b);
	}

	// If this for-stmt has a label, register break/continue targets in branch_regions
	if (fs->label != nullptr) {
		Ast *label = fs->label;
		for_array(i, b->branch_regions) {
			if (b->branch_regions[i].cond == label) {
				b->branch_regions[i].false_block = done_block; // break target
				b->branch_regions[i].true_block  = post_block; // continue target
				break;
			}
		}
	}

	// Jump to loop header
	fb_emit_jump(b, loop_block);
	fb_set_block(b, loop_block);

	// Condition check (if present)
	if (fs->cond != nullptr) {
		fbValue cond = fb_build_expr(b, fs->cond);
		fbValue cond_bool = fb_emit_conv(b, cond, t_bool);
		fb_emit_branch(b, cond_bool, body_block, done_block);
		fb_set_block(b, body_block);
	}

	// Push break/continue targets
	fbTargetList tl = {};
	tl.prev = b->target_list;
	tl.break_block = done_block;
	tl.continue_block = post_block;
	tl.scope_index = b->scope_index;
	tl.is_block = false;
	b->target_list = &tl;

	fb_build_stmt(b, fs->body);

	b->target_list = tl.prev;

	// Post block
	if (!fb_block_is_terminated(b)) {
		fb_emit_jump(b, post_block);
	}
	if (fs->post != nullptr) {
		fb_set_block(b, post_block);
		fb_build_stmt(b, fs->post);
		if (!fb_block_is_terminated(b)) {
			fb_emit_jump(b, loop_block);
		}
	}

	fb_set_block(b, done_block);
	fb_scope_close(b, fbDeferExit_Default, 0);
}

gb_internal void fb_build_when_stmt(fbBuilder *b, AstWhenStmt *ws) {
	TypeAndValue tv = type_and_value_of_expr(ws->cond);
	GB_ASSERT(tv.value.kind == ExactValue_Bool);
	if (tv.value.value_bool) {
		fb_build_stmt_list(b, ws->body->BlockStmt.stmts);
	} else if (ws->else_stmt) {
		switch (ws->else_stmt->kind) {
		case Ast_BlockStmt:
			fb_build_stmt_list(b, ws->else_stmt->BlockStmt.stmts);
			break;
		case Ast_WhenStmt:
			fb_build_when_stmt(b, &ws->else_stmt->WhenStmt);
			break;
		default:
			GB_PANIC("fb_build_when_stmt: unexpected else kind");
			break;
		}
	}
}

// ───── Switch statement ─────

gb_internal bool fb_switch_can_be_trivial(AstSwitchStmt *ss) {
	if (ss->tag == nullptr) return false;

	TypeAndValue tv = type_and_value_of_expr(ss->tag);
	if (!is_type_integer(core_type(tv.type)) && !is_type_enum(tv.type) && !is_type_boolean(tv.type)) {
		return false;
	}

	ast_node(body, BlockStmt, ss->body);
	for (Ast *clause : body->stmts) {
		ast_node(cc, CaseClause, clause);
		for (Ast *expr : cc->list) {
			expr = unparen_expr(expr);
			if (is_ast_range(expr)) return false;
			TypeAndValue etv = type_and_value_of_expr(expr);
			if (etv.mode != Addressing_Constant) return false;
		}
	}
	return true;
}

gb_internal void fb_build_switch_stmt(fbBuilder *b, Ast *node) {
	ast_node(ss, SwitchStmt, node);

	fb_scope_open(b, ss->scope);

	if (ss->init != nullptr) {
		fb_build_stmt(b, ss->init);
	}

	// Evaluate tag expression, or constant true for tag-less switches.
	fbValue tag = {};
	Type *tag_type = nullptr;
	if (ss->tag != nullptr) {
		tag = fb_build_expr(b, ss->tag);
		tag_type = type_of_expr(ss->tag);
	} else {
		tag = fb_emit_iconst(b, t_bool, 1);
		tag_type = t_bool;
	}

	u32 done_block = fb_new_block(b);

	ast_node(body, BlockStmt, ss->body);
	isize case_count = body->stmts.count;

	// Pre-allocate a body block per case clause.
	auto body_blocks = slice_make<u32>(heap_allocator(), case_count);
	auto body_scopes = slice_make<Scope *>(heap_allocator(), case_count);
	i32 default_idx = -1;
	for_array(i, body->stmts) {
		ast_node(cc, CaseClause, body->stmts[i]);
		body_blocks[i] = fb_new_block(b);
		body_scopes[i] = cc->scope;
		if (cc->list.count == 0) {
			default_idx = cast(i32)i;
		}
	}

	u32 default_block = (default_idx >= 0) ? body_blocks[default_idx] : done_block;

	// ── Dispatch: trivial (FB_SWITCH) or chain-of-comparisons ──

	bool is_trivial = fb_switch_can_be_trivial(ss);

	if (is_trivial) {
		// Emit FB_SWITCH instruction: key=tag, default_block, cases via aux.
		u32 aux_start = b->proc->aux_count;
		u32 total_cases = 0;
		for_array(i, body->stmts) {
			ast_node(cc, CaseClause, body->stmts[i]);
			for (Ast *expr : cc->list) {
				expr = unparen_expr(expr);
				TypeAndValue etv = type_and_value_of_expr(expr);
				i64 key = exact_value_to_i64(etv.value);
				fb_aux_push(b->proc, cast(u32)cast(i32)key);
				fb_aux_push(b->proc, body_blocks[i]);
				total_cases++;
			}
		}
		fb_inst_emit(b->proc, FB_SWITCH, FB_VOID, tag.id, default_block, aux_start, 0, cast(i64)total_cases);
	} else {
		// Chain of CMP + BRANCH per case value.
		for_array(i, body->stmts) {
			ast_node(cc, CaseClause, body->stmts[i]);
			if (cc->list.count == 0) continue; // default handled at end

			for (Ast *expr : cc->list) {
				expr = unparen_expr(expr);
				u32 next_cond = fb_new_block(b);

				fbValue cond = {};
				if (is_ast_range(expr)) {
					ast_node(re, BinaryExpr, expr);
					fbValue lhs = fb_build_expr(b, re->left);
					fbValue rhs = fb_build_expr(b, re->right);

					// lower <= tag
					bool is_signed = fb_type_is_signed(tag_type);
					bool is_float = is_type_float(tag_type);
					fbOp ge_op, upper_op;
					if (is_float) {
						ge_op = FB_CMP_FGE;
						upper_op = (re->op.kind == Token_RangeHalf) ? FB_CMP_FLT : FB_CMP_FLE;
					} else {
						ge_op = is_signed ? FB_CMP_SGE : FB_CMP_UGE;
						upper_op = (re->op.kind == Token_RangeHalf)
							? (is_signed ? FB_CMP_SLT : FB_CMP_ULT)
							: (is_signed ? FB_CMP_SLE : FB_CMP_ULE);
					}
					fbValue cond_lo = fb_emit_cmp(b, ge_op, tag, lhs);
					fbValue cond_hi = fb_emit_cmp(b, upper_op, tag, rhs);
					// AND the two conditions
					cond = fb_emit_arith(b, FB_AND, cond_lo, cond_hi, t_bool);
				} else {
					fbValue case_val = fb_build_expr(b, expr);
					bool is_float = is_type_float(tag_type);
					fbOp eq_op = is_float ? FB_CMP_FEQ : FB_CMP_EQ;
					cond = fb_emit_cmp(b, eq_op, tag, case_val);
				}
				fb_emit_branch(b, cond, body_blocks[i], next_cond);
				fb_set_block(b, next_cond);
			}
		}
		// Fall through to default.
		fb_emit_jump(b, default_block);
	}

	// ── Emit case bodies ──

	// Set up label if present — update the pre-populated entry from fb_procedure_begin.
	if (ss->label != nullptr) {
		for_array(i, b->branch_regions) {
			if (b->branch_regions[i].cond == ss->label) {
				b->branch_regions[i].false_block = done_block;  // break target
				b->branch_regions[i].true_block = 0;            // no continue in switch
				break;
			}
		}
	}

	for_array(i, body->stmts) {
		ast_node(cc, CaseClause, body->stmts[i]);

		u32 fall = done_block;
		if (i + 1 < cast(isize)case_count) {
			fall = body_blocks[i + 1];
		}

		fb_set_block(b, body_blocks[i]);

		fbTargetList tl = {};
		tl.prev = b->target_list;
		tl.break_block = done_block;
		tl.continue_block = 0;
		tl.fallthrough_block = fall;
		tl.scope_index = b->scope_index;
		tl.is_block = false;
		b->target_list = &tl;

		fb_scope_open(b, body_scopes[i]);
		fb_build_stmt_list(b, cc->stmts);
		fb_scope_close(b, fbDeferExit_Default, 0);

		b->target_list = tl.prev;

		if (!fb_block_is_terminated(b)) {
			fb_emit_jump(b, done_block);
		}
	}

	fb_set_block(b, done_block);
	fb_scope_close(b, fbDeferExit_Default, 0);

	gb_free(heap_allocator(), body_blocks.data);
	gb_free(heap_allocator(), body_scopes.data);
}

gb_internal void fb_build_type_switch_stmt(fbBuilder *b, Ast *node) {
	ast_node(ss, TypeSwitchStmt, node);

	fb_scope_open(b, ss->scope);

	// Extract the tag assignment: "v in expr" or "&v in expr".
	ast_node(as, AssignStmt, ss->tag);
	Ast *rhs = as->rhs[0];

	// Build the union expression and obtain a pointer to it.
	fbValue parent = fb_build_expr(b, rhs);
	Type *parent_type = parent.type;
	bool is_parent_ptr = is_type_pointer(parent_type);
	Type *ut = base_type(type_deref(parent_type));

	TypeSwitchKind switch_kind = check_valid_type_switch_type(parent_type);
	bool is_any = (switch_kind == TypeSwitch_Any);

	// Get a pointer to the subject (union or any).
	fbValue subject_ptr = parent;
	if (is_parent_ptr) {
		subject_ptr = fb_emit_load(b, parent, type_deref(parent_type));
	}

	fbValue tag = {};
	fbValue union_ptr = {}; // only used for union paths
	bool is_maybe_ptr = false;
	bool is_zero_sized = false;

	if (is_any) {
		// any is {data: rawptr, id: typeid}. Load the id field for dispatch.
		subject_ptr.type = alloc_type_pointer(ut);
		i64 ptr_sz = build_context.ptr_size;
		fbValue id_ptr = fb_emit_member(b, subject_ptr, ptr_sz);
		tag = fb_emit_load(b, id_ptr, t_typeid);
	} else {
		GB_ASSERT(switch_kind == TypeSwitch_Union);
		union_ptr = subject_ptr;
		union_ptr.type = alloc_type_pointer(ut);

		// Preload the tag for dispatch.
		type_size_of(ut); // ensure layout cached
		is_maybe_ptr = is_type_union_maybe_pointer(ut);
		is_zero_sized = (type_size_of(ut) == 0);

		if (is_maybe_ptr) {
			// Maybe-pointer union: load the data pointer (which IS the data).
			Type *variant_type = ut->Union.variants[0];
			fbValue data_ptr = union_ptr;
			data_ptr.type = alloc_type_pointer(variant_type);
			fbValue data = fb_emit_load(b, data_ptr, variant_type);
			// Convert to rawptr for nil comparison.
			data.type = t_rawptr;
			tag = data;
		} else if (!is_zero_sized) {
			// Regular union: load tag from union_ptr + variant_block_size.
			i64 tag_offset = ut->Union.variant_block_size.load(std::memory_order_relaxed);
			Type *tag_type = union_tag_type(ut);
			fbValue tag_ptr = fb_emit_member(b, union_ptr, tag_offset);
			tag = fb_emit_load(b, tag_ptr, tag_type);
		}
	}

	u32 done_block = fb_new_block(b);

	ast_node(body, BlockStmt, ss->body);
	isize case_count = body->stmts.count;

	// Pre-allocate a body block and scope per case clause.
	auto body_blocks = slice_make<u32>(heap_allocator(), case_count);
	auto body_scopes = slice_make<Scope *>(heap_allocator(), case_count);
	i32 default_idx = -1;
	for_array(i, body->stmts) {
		ast_node(cc, CaseClause, body->stmts[i]);
		body_blocks[i] = fb_new_block(b);
		body_scopes[i] = cc->scope;
		if (cc->list.count == 0) {
			default_idx = cast(i32)i;
		}
	}

	u32 default_block = (default_idx >= 0) ? body_blocks[default_idx] : done_block;

	// ── Dispatch: chain of comparisons ──
	for_array(i, body->stmts) {
		ast_node(cc, CaseClause, body->stmts[i]);
		if (cc->list.count == 0) continue; // default handled at end

		for (Ast *type_expr : cc->list) {
			u32 next_cond = fb_new_block(b);
			Type *case_type = type_of_expr(type_expr);
			fbValue cond = {};

			if (is_any) {
				// any: compare typeid against compile-time hash.
				if (is_type_untyped_nil(case_type)) {
					fbValue nil_id = fb_emit_iconst(b, t_typeid, 0);
					cond = fb_emit_cmp(b, FB_CMP_EQ, tag, nil_id);
				} else {
					u64 case_id = type_hash_canonical_type(case_type);
					fbValue case_tag = fb_emit_iconst(b, t_typeid, cast(i64)case_id);
					cond = fb_emit_cmp(b, FB_CMP_EQ, tag, case_tag);
				}
			} else if (is_maybe_ptr) {
				// Maybe-pointer: nil → compare data == 0, variant → compare data != 0.
				fbValue nil_val = fb_emit_iconst(b, t_rawptr, 0);
				if (is_type_untyped_nil(case_type)) {
					cond = fb_emit_cmp(b, FB_CMP_EQ, tag, nil_val);
				} else {
					cond = fb_emit_cmp(b, FB_CMP_NE, tag, nil_val);
				}
			} else if (is_zero_sized) {
				// Zero-sized union: never matches.
				cond = fb_emit_iconst(b, t_bool, 0);
			} else {
				// Regular union: compare tag against variant index.
				Type *tag_type = union_tag_type(ut);
				fbValue case_tag;
				if (is_type_untyped_nil(case_type)) {
					case_tag = fb_emit_iconst(b, tag_type, 0);
				} else {
					case_tag = fb_emit_iconst(b, tag_type, union_variant_index(ut, case_type));
				}
				cond = fb_emit_cmp(b, FB_CMP_EQ, tag, case_tag);
			}
			fb_emit_branch(b, cond, body_blocks[i], next_cond);
			fb_set_block(b, next_cond);
		}
	}
	// Fall through to default.
	fb_emit_jump(b, default_block);

	// ── Emit case bodies ──

	// Set up label if present — update the pre-populated entry from fb_procedure_begin.
	if (ss->label != nullptr) {
		for_array(i, b->branch_regions) {
			if (b->branch_regions[i].cond == ss->label) {
				b->branch_regions[i].false_block = done_block;  // break target
				b->branch_regions[i].true_block = 0;            // no continue in switch
				break;
			}
		}
	}

	for_array(i, body->stmts) {
		ast_node(cc, CaseClause, body->stmts[i]);

		fb_set_block(b, body_blocks[i]);

		fbTargetList tl = {};
		tl.prev = b->target_list;
		tl.break_block = done_block;
		tl.continue_block = 0;
		tl.fallthrough_block = 0;
		tl.scope_index = b->scope_index;
		tl.is_block = false;
		b->target_list = &tl;

		fb_scope_open(b, body_scopes[i]);

		// Bind the implicit entity for this case.
		Entity *case_entity = implicit_entity_of_node(body->stmts[i]);
		if (case_entity != nullptr) {
			Type *entity_type = case_entity->type;
			bool by_value = (case_entity->flags & EntityFlag_Value) != 0;
			bool is_single_variant = (cc->list.count == 1 && !is_type_untyped_nil(type_of_expr(cc->list[0])));

			if (is_any) {
				// any type switch: data pointer is field 0 of the any struct.
				if (is_single_variant && !is_type_untyped_nil(entity_type)) {
					// Load the data rawptr from field 0.
					fbValue data_ptr = fb_emit_member(b, subject_ptr, 0);
					fbValue data = fb_emit_load(b, data_ptr, t_rawptr);
					// data is rawptr → reinterpret as ^case_type.
					data.type = alloc_type_pointer(entity_type);

					if (by_value) {
						fbAddr local = fb_add_local(b, entity_type, case_entity, false);
						fb_emit_copy_value(b, local.base, fb_addr_load(b, fbAddr{fbAddr_Default, data, entity_type}), entity_type);
					} else {
						fbAddr addr = {};
						addr.kind = fbAddr_Default;
						addr.base = data;
						addr.type = entity_type;
						map_set(&b->variable_map, case_entity, addr);
					}
				} else {
					// Default or nil case: entity is the full any type.
					if (by_value) {
						fbAddr local = fb_add_local(b, entity_type, case_entity, false);
						fb_emit_copy_value(b, local.base, fb_addr_load(b, fbAddr{fbAddr_Default, subject_ptr, ut}), entity_type);
					} else {
						fbAddr addr = {};
						addr.kind = fbAddr_Default;
						addr.base = subject_ptr;
						addr.base.type = alloc_type_pointer(entity_type);
						addr.type = entity_type;
						map_set(&b->variable_map, case_entity, addr);
					}
				}
			} else if (is_single_variant && !is_type_untyped_nil(entity_type)) {
				// Single variant case: entity is typed as the variant.
				if (by_value) {
					// By-value: allocate local, copy variant data from union.
					fbAddr local = fb_add_local(b, entity_type, case_entity, false);
					fbValue src_ptr = union_ptr;
					src_ptr.type = alloc_type_pointer(entity_type);
					fb_emit_copy_value(b, local.base, fb_addr_load(b, fbAddr{fbAddr_Default, src_ptr, entity_type}), entity_type);
				} else {
					// By-reference: point directly at union data, retyped.
					fbAddr addr = {};
					addr.kind = fbAddr_Default;
					addr.base = union_ptr;
					addr.base.type = alloc_type_pointer(entity_type);
					addr.type = entity_type;
					map_set(&b->variable_map, case_entity, addr);
				}
			} else {
				// Default, multi-case, or nil case: entity is the full union type.
				if (by_value) {
					fbAddr local = fb_add_local(b, entity_type, case_entity, false);
					fb_emit_copy_value(b, local.base, fb_addr_load(b, fbAddr{fbAddr_Default, union_ptr, ut}), entity_type);
				} else {
					fbAddr addr = {};
					addr.kind = fbAddr_Default;
					addr.base = union_ptr;
					addr.base.type = alloc_type_pointer(entity_type);
					addr.type = entity_type;
					map_set(&b->variable_map, case_entity, addr);
				}
			}
		}

		fb_build_stmt_list(b, cc->stmts);
		fb_scope_close(b, fbDeferExit_Default, 0);

		b->target_list = tl.prev;

		if (!fb_block_is_terminated(b)) {
			fb_emit_jump(b, done_block);
		}
	}

	fb_set_block(b, done_block);
	fb_scope_close(b, fbDeferExit_Default, 0);

	gb_free(heap_allocator(), body_blocks.data);
	gb_free(heap_allocator(), body_scopes.data);
}

gb_internal void fb_build_stmt(fbBuilder *b, Ast *node) {
	if (node == nullptr) return;

	// If we're in a terminated block, don't emit more instructions
	if (fb_block_is_terminated(b)) return;

	switch (node->kind) {
	case Ast_EmptyStmt:
		break;

	case Ast_UsingStmt:
		break;

	case Ast_BlockStmt: {
		ast_node(bs, BlockStmt, node);
		u32 done_block = FB_NOREG;
		fbTargetList *tl_ptr = nullptr;
		fbTargetList tl = {};

		if (bs->label != nullptr) {
			done_block = fb_new_block(b);
			tl.prev = b->target_list;
			tl.break_block = done_block;
			tl.continue_block = 0;
			tl.scope_index = b->scope_index;
			tl.is_block = true;
			b->target_list = &tl;
			tl_ptr = &tl;

			// Register break target in branch_regions for labeled break
			for_array(i, b->branch_regions) {
				if (b->branch_regions[i].cond == bs->label) {
					b->branch_regions[i].false_block = done_block;
					break;
				}
			}
		}

		fb_scope_open(b, bs->scope);
		fb_build_stmt_list(b, bs->stmts);
		fb_scope_close(b, fbDeferExit_Default, 0);

		if (done_block != FB_NOREG) {
			if (!fb_block_is_terminated(b)) {
				fb_emit_jump(b, done_block);
			}
			fb_set_block(b, done_block);
			b->target_list = tl.prev;
		}
		break;
	}

	case Ast_WhenStmt: {
		ast_node(ws, WhenStmt, node);
		fb_build_when_stmt(b, ws);
		break;
	}

	case Ast_ValueDecl: {
		ast_node(vd, ValueDecl, node);
		if (vd->is_mutable) {
			fb_build_mutable_value_decl(b, node);
		} else {
			fb_build_constant_value_decl(b, vd);
		}
		break;
	}

	case Ast_ReturnStmt: {
		ast_node(rs, ReturnStmt, node);
		fb_build_return_stmt(b, rs->results);
		break;
	}

	case Ast_ExprStmt: {
		ast_node(es, ExprStmt, node);
		fb_build_expr(b, es->expr);
		break;
	}

	case Ast_AssignStmt: {
		ast_node(as, AssignStmt, node);
		fb_build_assign_stmt(b, as);
		break;
	}

	case Ast_IfStmt:
		fb_build_if_stmt(b, node);
		break;

	case Ast_ForStmt:
		fb_build_for_stmt(b, node);
		break;

	case Ast_RangeStmt:
		fb_build_range_stmt(b, node);
		break;

	case Ast_BranchStmt: {
		ast_node(bs, BranchStmt, node);
		u32 target_block = 0;
		i32 target_scope = b->scope_index;

		if (bs->label != nullptr) {
			// Labeled break/continue: resolve the Ast_Ident through its entity
			// to get e->Label.node (an Ast_Label), then look up in branch_regions.
			Entity *label_entity = entity_of_node(bs->label);
			Ast *label_node = (label_entity != nullptr) ? label_entity->Label.node : nullptr;
			for_array(i, b->branch_regions) {
				if (b->branch_regions[i].cond == label_node) {
					switch (bs->token.kind) {
					case Token_break:    target_block = b->branch_regions[i].false_block; break;
					case Token_continue: target_block = b->branch_regions[i].true_block;  break;
					default: break;
					}
					break;
				}
			}
			// For labeled branches, find the target scope from the target list
			for (fbTargetList *t = b->target_list; t != nullptr; t = t->prev) {
				if (t->break_block == target_block || t->continue_block == target_block) {
					target_scope = t->scope_index;
					break;
				}
			}
		} else {
			for (fbTargetList *t = b->target_list; t != nullptr; t = t->prev) {
				if (t->is_block) continue;

				switch (bs->token.kind) {
				case Token_break:       target_block = t->break_block;       break;
				case Token_continue:    target_block = t->continue_block;    break;
				case Token_fallthrough: target_block = t->fallthrough_block; break;
				default: break;
				}
				if (target_block != 0) {
					target_scope = t->scope_index;
					break;
				}
			}
		}

		if (target_block != 0) {
			fb_emit_defer_stmts(b, fbDeferExit_Branch, target_scope);
			fb_emit_jump(b, target_block);
		}
		break;
	}

	case Ast_SwitchStmt:
		fb_build_switch_stmt(b, node);
		break;

	case Ast_TypeSwitchStmt:
		fb_build_type_switch_stmt(b, node);
		break;

	case Ast_DeferStmt: {
		ast_node(ds, DeferStmt, node);
		fbDefer *d = array_add_and_get(&b->defer_stack);
		d->kind = fbDefer_Node;
		d->scope_index = b->scope_index;
		d->block = b->current_block;
		d->stmt = ds->stmt;
		break;
	}

	default:
		GB_PANIC("TODO fb_build_stmt %.*s", LIT(ast_strings[node->kind]));
		break;
	}
}

// ───────────────────────────────────────────────────────────────────────
// Step 6: Procedure lifecycle
// ───────────────────────────────────────────────────────────────────────

gb_internal void fb_procedure_begin(fbBuilder *b) {
	Entity *e = b->entity;
	DeclInfo *decl = decl_info_of_entity(e);
	b->decl = decl;

	if (decl == nullptr || decl->proc_lit == nullptr) {
		b->body = nullptr;
		return;
	}

	Ast *pl = decl->proc_lit;
	b->body = pl->ProcLit.body;
	if (b->body == nullptr) return;

	Type *pt = base_type(e->type);
	b->type = e->type;
	GB_ASSERT(pt->kind == Type_Proc);
	TypeProc *proc_type = &pt->Proc;

	// Initialize branch regions from decl labels
	if (decl != nullptr) {
		for_array(i, decl->labels) {
			BlockLabel bl = decl->labels[i];
			fbBranchRegions bb = {};
			bb.cond = bl.label;
			bb.true_block = 0;
			bb.false_block = 0;
			array_add(&b->branch_regions, bb);
		}
	}

	// Create entry block
	u32 entry = fb_block_create(b->proc);
	fb_block_start(b->proc, entry);
	b->current_block = entry;

	// Set up parameter receiving
	fb_setup_params(b->proc);

	// Register parameter entities in the variable_map
	TypeTuple *params = proc_type->params ? &proc_type->params->Tuple : nullptr;
	if (params != nullptr) {
		for_array(i, params->variables) {
			Entity *param_e = params->variables[i];
			if (param_e == nullptr || param_e->kind != Entity_Variable) continue;

			// Find this entity's slot in param_locs
			bool found = false;
			for (u32 pi = 0; pi < b->proc->param_count; pi++) {
				u32 slot_idx = b->proc->param_locs[pi].slot_idx;
				fbStackSlot *slot = &b->proc->slots[slot_idx];
				if (slot->entity == param_e) {
					fbValue ptr = fb_emit_alloca_from_slot(b, slot_idx);

					// For MEMORY class params (unions, large structs), the slot
					// holds a pointer to the caller's data. Load the pointer and
					// use it as the base so accesses go through to the actual data.
					fbABIParamInfo abi = fb_abi_classify_type_sysv(param_e->type);
					if (abi.classes[0] == FB_ABI_MEMORY) {
						ptr = fb_emit_load(b, ptr, alloc_type_pointer(param_e->type));
					}

					fbAddr addr = {};
					addr.kind = fbAddr_Default;
					addr.base = ptr;
					addr.type = param_e->type;
					map_set(&b->variable_map, param_e, addr);
					found = true;
					break;
				}
			}
			if (!found && b->proc->xmm_param_count > 0) {
				// Search XMM param slots (non-Odin CC float params)
				for (u32 xi = 0; xi < b->proc->xmm_param_count; xi++) {
					u32 slot_idx = b->proc->xmm_param_locs[xi].slot_idx;
					fbStackSlot *slot = &b->proc->slots[slot_idx];
					if (slot->entity == param_e) {
						fbValue ptr = fb_emit_alloca_from_slot(b, slot_idx);
						fbAddr addr = {};
						addr.kind = fbAddr_Default;
						addr.base = ptr;
						addr.type = param_e->type;
						map_set(&b->variable_map, param_e, addr);
						found = true;
						break;
					}
				}
			}
			if (!found && b->proc->stack_param_count > 0) {
				// Search stack-passed param slots (overflow beyond 6 GP registers)
				for (u32 si = 0; si < b->proc->stack_param_count; si++) {
					u32 slot_idx = b->proc->stack_param_locs[si].slot_idx;
					fbStackSlot *slot = &b->proc->slots[slot_idx];
					if (slot->entity == param_e) {
						fbValue ptr = fb_emit_alloca_from_slot(b, slot_idx);

						// For MEMORY class params, the slot holds a pointer to
						// the caller's data. Load the pointer to get the actual base.
						fbABIParamInfo abi = fb_abi_classify_type_sysv(param_e->type);
						if (abi.classes[0] == FB_ABI_MEMORY) {
							ptr = fb_emit_load(b, ptr, alloc_type_pointer(param_e->type));
						}

						fbAddr addr = {};
						addr.kind = fbAddr_Default;
						addr.base = ptr;
						addr.type = param_e->type;
						map_set(&b->variable_map, param_e, addr);
						found = true;
						break;
					}
				}
			}
		}
	}

	// Odin CC: register context pointer.
	// The context pointer is the last parameter slot — either in GP register
	// params or in stack-passed params if registers overflowed.
	if (proc_type->calling_convention == ProcCC_Odin) {
		u32 ctx_slot = 0;
		bool ctx_found = false;

		// Check GP register params first (context is last when it fits)
		if (b->proc->param_count > 0) {
			u32 last_slot = b->proc->param_locs[b->proc->param_count - 1].slot_idx;
			fbStackSlot *slot = &b->proc->slots[last_slot];
			if (slot->entity == nullptr && slot->odin_type == nullptr) {
				ctx_slot = last_slot;
				ctx_found = true;
			}
		}

		// Check stack-passed params (context overflowed to stack)
		if (!ctx_found && b->proc->stack_param_count > 0) {
			u32 last_slot = b->proc->stack_param_locs[b->proc->stack_param_count - 1].slot_idx;
			fbStackSlot *slot = &b->proc->slots[last_slot];
			if (slot->entity == nullptr && slot->odin_type == nullptr) {
				ctx_slot = last_slot;
				ctx_found = true;
			}
		}

		if (ctx_found) {
			fbValue ctx_ptr = fb_emit_alloca_from_slot(b, ctx_slot);
			fbAddr ctx_addr = {};
			ctx_addr.kind = fbAddr_Default;
			ctx_addr.base = ctx_ptr;
			ctx_addr.type = t_rawptr; // Context pointer

			fbContextData *cd = array_add_and_get(&b->context_stack);
			cd->ctx = ctx_addr;
			cd->uses_default = true;
		}
	}

	// Handle named results: create locals with default values
	if (proc_type->has_named_results && proc_type->results != nullptr) {
		auto const &results = proc_type->results->Tuple.variables;
		for_array(i, results) {
			Entity *re = results[i];
			if (re->kind != Entity_Variable) continue;
			if (is_blank_ident(re->token)) continue;
			fb_add_local(b, re->type, re, true);
		}
	}
}

gb_internal void fb_procedure_end(fbBuilder *b) {
	if (b->body == nullptr) return;

	// If the current block is not terminated, add an implicit return
	if (!fb_block_is_terminated(b)) {
		Type *pt = base_type(b->type);
		GB_ASSERT(pt->kind == Type_Proc);
		TypeProc *proc_type = &pt->Proc;

		if (proc_type->result_count == 0) {
			fb_emit_ret_void(b);
		} else {
			fb_inst_emit(b->proc, FB_UNREACHABLE, FB_VOID, FB_NOREG, FB_NOREG, FB_NOREG, 0, 0);
		}
	}
}

gb_internal void fb_procedure_generate(fbBuilder *b) {
	fb_procedure_begin(b);
	if (b->body == nullptr) return;

	// Entry point: inject __$startup_runtime call before the user body
	if (b->is_entry_point && b->module->startup_proc_idx != FB_NOREG) {
		fbValue sym = fb_emit_symaddr(b, b->module->startup_proc_idx);
		fb_inst_emit(b->proc, FB_CALL, FB_VOID, sym.id, b->proc->aux_count, 0, 0, 0);
	}

	fb_build_stmt(b, b->body);
	fb_procedure_end(b);
}

// ───────────────────────────────────────────────────────────────────────
// Step 7: Wire up fb_generate_procedures
// ───────────────────────────────────────────────────────────────────────

gb_internal void fb_generate_procedures(fbModule *m) {
	CheckerInfo *info = m->info;

	// Initialize entity → proc index map
	if (!fb_entity_proc_map_inited) {
		map_init(&fb_entity_proc_map);
		fb_entity_proc_map_inited = true;
	} else {
		map_clear(&fb_entity_proc_map);
	}

	// First pass: create all procedure objects (including foreign declarations)
	for (Entity *e : info->entities) {
		Scope *scope = e->scope;

		if ((scope->flags & ScopeFlag_File) == 0) {
			continue;
		}
		if (e->kind != Entity_Procedure) {
			continue;
		}
		if (e->min_dep_count.load(std::memory_order_relaxed) == 0) {
			continue;
		}

		fbProc *p = fb_proc_create(m, e);

		// Entry point needs global linkage
		if (e == info->entry_point) {
			p->is_export = true;
		}
		// Respect linkage="strong" — these procs need global visibility
		if (e->flags & EntityFlag_CustomLinkage_Strong) {
			p->is_export = true;
		}

		u32 proc_idx = cast(u32)m->procs.count;
		array_add(&m->procs, p);

		// Register in entity map
		map_set(&fb_entity_proc_map, e, proc_idx);
	}

	// Generate __$startup_runtime and __$cleanup_runtime stubs.
	// The runtime declares these as foreign (signatures only), but every backend
	// must synthesize implementations. The bodies are just `ret` for now.
	for_array(i, m->procs) {
		fbProc *p = m->procs[i];
		if (!p->is_foreign) continue;

		bool is_startup = str_eq(p->name, str_lit("__$startup_runtime"));
		bool is_cleanup = str_eq(p->name, str_lit("__$cleanup_runtime"));
		if (!is_startup && !is_cleanup) continue;

		// Convert from foreign declaration to defined stub with global visibility
		p->is_foreign = false;
		p->is_export  = true;

		p->inst_cap  = 8;
		p->insts     = gb_alloc_array(heap_allocator(), fbInst, p->inst_cap);
		p->block_cap = 2;
		p->blocks    = gb_alloc_array(heap_allocator(), fbBlock, p->block_cap);
		p->slot_cap  = 1;
		p->slots     = gb_alloc_array(heap_allocator(), fbStackSlot, p->slot_cap);
		p->aux_cap   = 4;
		p->aux       = gb_alloc_array(heap_allocator(), u32, p->aux_cap);
		p->loc_cap   = 2;
		p->locs      = gb_alloc_array(heap_allocator(), fbLoc, p->loc_cap);

		u32 entry = fb_block_create(p);
		fb_block_start(p, entry);
		fb_inst_emit(p, FB_RET, FB_VOID, FB_NOREG, FB_NOREG, FB_NOREG, 0, 0);
	}

	// Find key proc indices for entry point wiring
	m->startup_proc_idx = FB_NOREG;
	m->entry_proc_idx   = FB_NOREG;
	for_array(i, m->procs) {
		fbProc *p = m->procs[i];
		if (str_eq(p->name, str_lit("__$startup_runtime"))) {
			m->startup_proc_idx = cast(u32)i;
		}
		if (p->entity == info->entry_point) {
			m->entry_proc_idx = cast(u32)i;
		}
	}

	// Discover global variables before building procedure IR, so that
	// entity references to globals can be resolved during expr building.
	fb_generate_globals(m);

	// Install signal handlers for graceful fallback on unsupported features.
	// SIGILL: from __builtin_trap() in GB_PANIC/GB_ASSERT
	// SIGSEGV: from null deref after partial IR generation
	// SIGABRT: from abort() calls
	struct sigaction sa_new = {}, sa_old_ill = {}, sa_old_segv = {}, sa_old_abrt = {};
	sa_new.sa_handler = fb_recovery_signal_handler;
	sa_new.sa_flags = 0;
	sigemptyset(&sa_new.sa_mask);
	sigaction(SIGILL, &sa_new, &sa_old_ill);
	sigaction(SIGSEGV, &sa_new, &sa_old_segv);
	sigaction(SIGABRT, &sa_new, &sa_old_abrt);

	i32 stub_count = 0;

	// Second pass: generate IR from AST for non-foreign, non-stub procedures
	for_array(i, m->procs) {
		fbProc *p = m->procs[i];
		if (p->is_foreign) continue;
		if (p->inst_count > 0) continue; // skip stubs already populated

		bool is_entry = (p->entity == info->entry_point);

		// Build IR from AST
		fbBuilder b = {};
		b.proc = p;
		b.module = m;
		b.entity = p->entity;
		b.type = p->odin_type;
		b.is_foreign = p->is_foreign;
		b.is_export = p->is_export;
		b.is_entry_point = is_entry;
		b.target_list = nullptr;
		b.scope_index = 0;
		b.current_block = 0;

		array_init(&b.scope_stack, heap_allocator());
		array_init(&b.context_stack, heap_allocator());
		array_init(&b.defer_stack, heap_allocator());
		array_init(&b.branch_regions, heap_allocator());
		map_init(&b.variable_map);
		map_init(&b.soa_values_map);

		// Try to generate the procedure; on assertion failure, fall back to stub
		fb_recovery_active = true;
		if (sigsetjmp(fb_recovery_buf, 1) == 0) {
			fb_procedure_generate(&b);
			fb_recovery_active = false;
		} else {
			// Recovery: assertion fired during generation.
			// Reset the proc to an empty stub.
			stub_count++;
			p->inst_count = 0;
			p->block_count = 0;
			p->slot_count = 0;
			p->aux_count = 0;
			p->next_value = 0;
			p->param_count = 0;
			p->xmm_param_count = 0;
			p->stack_param_count = 0;

			u32 bb0 = fb_block_create(p);
			fb_block_start(p, bb0);
			fb_inst_emit(p, FB_RET, FB_VOID, FB_NOREG, FB_NOREG, FB_NOREG, 0, 0);
		}

		// Cleanup builder
		array_free(&b.scope_stack);
		array_free(&b.context_stack);
		array_free(&b.defer_stack);
		array_free(&b.branch_regions);
		map_destroy(&b.variable_map);
		map_destroy(&b.soa_values_map);
	}

	// Restore original signal handlers
	sigaction(SIGILL, &sa_old_ill, nullptr);
	sigaction(SIGSEGV, &sa_old_segv, nullptr);
	sigaction(SIGABRT, &sa_old_abrt, nullptr);

	if (stub_count > 0) {
		gb_printf_err("fast backend: %d procedure(s) stubbed due to unsupported features\n", stub_count);
	}
}

// ───────────────────────────────────────────────────────────────────────
// Global variable support
// ───────────────────────────────────────────────────────────────────────

// Serialize a constant ExactValue into a byte buffer for .data.
// Returns a heap-allocated buffer of `size` bytes, or NULL if unsupported.
gb_internal u8 *fb_serialize_const_value(ExactValue value, u32 size) {
	u8 *buf = gb_alloc_array(heap_allocator(), u8, size);
	gb_zero_size(buf, size);

	switch (value.kind) {
	case ExactValue_Bool: {
		buf[0] = value.value_bool ? 1 : 0;
		return buf;
	}
	case ExactValue_Integer: {
		u64 ival = exact_value_to_u64(value);
		gb_memmove(buf, &ival, gb_min(size, 8));
		return buf;
	}
	case ExactValue_Float: {
		f64 fval = value.value_float;
		if (size == 4) {
			f32 f32val = cast(f32)fval;
			gb_memmove(buf, &f32val, 4);
		} else if (size == 8) {
			gb_memmove(buf, &fval, 8);
		} else if (size == 2) {
			// f16: truncate from f64 via f32 → f16 bit pattern
			// For now just store zero for f16
			gb_zero_size(buf, 2);
		} else {
			gb_free(heap_allocator(), buf);
			return nullptr;
		}
		return buf;
	}
	case ExactValue_Pointer: {
		u64 pval = cast(u64)value.value_pointer;
		gb_memmove(buf, &pval, gb_min(size, 8));
		return buf;
	}
	default:
		gb_free(heap_allocator(), buf);
		return nullptr;
	}
}

gb_internal void fb_generate_globals(fbModule *m) {
	CheckerInfo *info = m->info;

	for (DeclInfo *d : info->variable_init_order) {
		Entity *e = d->entity;

		if ((e->scope->flags & ScopeFlag_File) == 0) {
			continue;
		}
		if (e->min_dep_count.load(std::memory_order_relaxed) == 0) {
			continue;
		}

		GB_ASSERT(e->kind == Entity_Variable);

		bool is_foreign = e->Variable.is_foreign;
		bool is_export  = e->Variable.is_export;

		String name = fb_get_entity_name(m, e);
		u32 size  = cast(u32)type_size_of(e->type);
		u32 align = cast(u32)type_align_of(e->type);
		if (align == 0) align = 1;

		fbGlobalEntry entry = {};
		entry.entity     = e;
		entry.name       = name;
		entry.odin_type  = e->type;
		entry.size       = size;
		entry.align      = align;
		entry.is_foreign = is_foreign;
		entry.is_export  = is_export;
		entry.init_data  = nullptr;

		if (!is_foreign && d->init_expr != nullptr) {
			TypeAndValue tav = type_and_value_of_expr(d->init_expr);
			if (tav.mode != Addressing_Invalid &&
			    tav.value.kind != ExactValue_Invalid &&
			    !is_type_any(e->type)) {
				entry.init_data = fb_serialize_const_value(tav.value, size);
			}
			// TODO: when init_data is NULL here, the global has a non-trivial initializer
			// (e.g. string, compound literal) that fb_serialize_const_value cannot handle.
			// It will stay zero until __$startup_runtime runs proper init code.
		}

		u32 global_idx = cast(u32)m->global_entries.count;
		array_add(&m->global_entries, entry);
		map_set(&m->global_entity_map, e, global_idx);

		// Register foreign libraries
		if (is_foreign && e->Variable.foreign_library != nullptr) {
			Entity *lib = e->Variable.foreign_library;
			if (lib->kind == Entity_LibraryName) {
				if (!ptr_set_update(&m->linker_data->foreign_libraries_set, lib)) {
					array_add(&m->linker_data->foreign_libraries, lib);
				}
			}
		}
	}
}
