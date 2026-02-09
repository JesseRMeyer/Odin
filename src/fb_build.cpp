// Fast Backend — AST walker: translates Odin AST into fast backend IR
//
// Mirrors the Tilde backend's cg_build_stmt / cg_build_expr pattern.

#include <setjmp.h>
#include <signal.h>

// Graceful fallback: catch assertion failures during procedure generation.
// When a proc uses unsupported features, the assert fires __builtin_trap()
// which raises SIGILL. We catch it and fall back to an empty stub.
// fb_recovery_active is defined in fb_ir.cpp (before fb_verify.h needs it).
gb_global thread_local sigjmp_buf fb_recovery_buf;

gb_global thread_local volatile const char *fb_recovery_proc_name = nullptr;
gb_global thread_local volatile int fb_recovery_last_line = 0;
gb_internal void fb_recovery_signal_handler(int sig) {
	if (fb_recovery_active) {
		gb_printf_err("  [recovery sig=%d proc=%s last_line=%d]\n", sig, fb_recovery_proc_name ? fb_recovery_proc_name : "?", fb_recovery_last_line);
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

// Forward declaration for type info (defined in fb_type_info.cpp)
gb_internal void    fb_generate_type_info(fbModule *m);
gb_internal isize   fb_type_info_index(CheckerInfo *info, Type *type, bool err_on_not_found = true);

// Forward declarations for functions used by map support before their definition
gb_internal void    fb_emit_copy_value(fbBuilder *b, fbValue dst_ptr, fbValue val, Type *type);
gb_internal fbValue fb_build_source_code_location(fbBuilder *b, String proc_name, TokenPos pos);
gb_internal u32     fb_gen_map_cell_info(fbModule *m, Type *type);
gb_internal fbValue fb_map_info_ptr(fbBuilder *b, Type *map_type);
gb_internal u32     fb_gen_hasher_proc(fbBuilder *b, Type *type);
gb_internal u32     fb_gen_equal_proc(fbBuilder *b, Type *type);
gb_internal fbValue fb_map_key_hash(fbBuilder *b, fbValue map_ptr, Type *map_type, fbValue key, fbValue *key_ptr_out);
gb_internal fbValue fb_dynamic_map_get(fbBuilder *b, fbValue map_ptr, Type *map_type, fbValue hash, fbValue key_ptr);
gb_internal void    fb_dynamic_map_set(fbBuilder *b, fbValue map_ptr, Type *map_type, fbValue hash, fbValue key_ptr, fbValue val_ptr, Ast *node);
gb_internal void    fb_dynamic_map_reserve(fbBuilder *b, fbValue map_ptr, Type *map_type, fbValue capacity, Ast *node);

// ───────────────────────────────────────────────────────────────────────
// Parameter setup: classify params via ABI, create stack slots, record param_locs
// ───────────────────────────────────────────────────────────────────────

gb_internal void fb_setup_params(fbProc *p) {
	Type *pt = base_type(p->odin_type);
	GB_ASSERT(pt != nullptr && pt->kind == Type_Proc);

	TypeProc *proc_type = &pt->Proc;
	bool is_odin_like = is_calling_convention_odin(proc_type->calling_convention);
	bool has_context  = (proc_type->calling_convention == ProcCC_Odin);

	if (proc_type->params == nullptr && !is_odin_like) {
		return;
	}

	i32 param_count = proc_type->param_count;

	// Determine split return count: for Odin CC with N results, the first
	// N-1 are returned via hidden output pointer parameters; the last is
	// returned in a register.
	TypeTuple *results = proc_type->results ? &proc_type->results->Tuple : nullptr;
	i32 result_count = results ? cast(i32)results->variables.count : 0;
	i32 split_count = (is_odin_like && result_count > 1) ? (result_count - 1) : 0;

	// Single MEMORY-class return needs a hidden output pointer parameter (sret).
	bool needs_sret = false;
	if (is_odin_like && result_count == 1 && split_count == 0 && results != nullptr) {
		Type *ret_type = results->variables[0]->type;
		fbType ret_ft = fb_data_type(ret_type);
		if (ret_ft.kind == FBT_VOID) needs_sret = true;
	}

	u32 max_gp_params = param_count + split_count + (has_context ? 1 : 0) + (needs_sret ? 1 : 0);
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
			if (!is_odin_like && xmm_idx < 8) {
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

	// Single MEMORY-class return: add hidden output pointer parameter.
	// This matches the caller-side sret_single aux push in fb_build_call_expr.
	if (needs_sret) {
		u32 slot = fb_slot_create(p, 8, 8, nullptr, results->variables[0]->type);
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
		p->sret_slot_idx = cast(i32)slot;
	}

	// Odin CC: append context pointer as the last GP parameter
	if (has_context) {
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
	GB_ASSERT(ptr.id != FB_NOREG);
	fbType ft = fb_data_type(elem_type);
	if (ft.kind == FBT_VOID) ft = FB_I64; // aggregate: load as i64
	u32 r = fb_inst_emit(b->proc, FB_LOAD, ft, ptr.id, FB_NOREG, FB_NOREG, 0, 0);
	return fb_make_value(r, elem_type);
}

gb_internal void fb_emit_store(fbBuilder *b, fbValue ptr, fbValue val) {
	GB_ASSERT(ptr.id != FB_NOREG);
	GB_ASSERT(val.id != FB_NOREG);
	fbType ft = FB_I64;
	if (val.type != nullptr) {
		ft = fb_data_type(val.type);
		if (ft.kind == FBT_VOID) ft = FB_I64;
	}
	fb_inst_emit(b->proc, FB_STORE, ft, ptr.id, val.id, FB_NOREG, 0, 0);
}

gb_internal fbValue fb_emit_alloca_from_slot(fbBuilder *b, u32 slot_idx) {
	GB_ASSERT(slot_idx < b->proc->slot_count);
	u32 r = fb_inst_emit(b->proc, FB_ALLOCA, FB_PTR, slot_idx, FB_NOREG, FB_NOREG, 0, 0);
	return fb_make_value(r, nullptr);
}

gb_internal void fb_emit_jump(fbBuilder *b, u32 target_block) {
	GB_ASSERT(target_block < b->proc->block_count);
	fb_inst_emit(b->proc, FB_JUMP, FB_VOID, target_block, FB_NOREG, FB_NOREG, 0, 0);
}

gb_internal void fb_emit_branch(fbBuilder *b, fbValue cond, u32 true_blk, u32 false_blk) {
	GB_ASSERT(cond.id != FB_NOREG);
	GB_ASSERT(true_blk < b->proc->block_count);
	GB_ASSERT(false_blk < b->proc->block_count);
	fb_inst_emit(b->proc, FB_BRANCH, FB_VOID, cond.id, true_blk, false_blk, 0, 0);
}

gb_internal void fb_emit_ret(fbBuilder *b, fbValue val) {
	fb_inst_emit(b->proc, FB_RET, FB_VOID, val.id, FB_NOREG, FB_NOREG, 0, 0);
}

gb_internal void fb_emit_ret_void(fbBuilder *b) {
	fb_inst_emit(b->proc, FB_RET, FB_VOID, FB_NOREG, FB_NOREG, FB_NOREG, 0, 0);
}

gb_internal fbValue fb_emit_arith(fbBuilder *b, fbOp op, fbValue lhs, fbValue rhs, Type *type) {
	GB_ASSERT(lhs.id != FB_NOREG);
	GB_ASSERT(rhs.id != FB_NOREG);
	fbType ft = fb_data_type(type);
	if (ft.kind == FBT_VOID) ft = FB_I64;
	u32 r = fb_inst_emit(b->proc, op, ft, lhs.id, rhs.id, FB_NOREG, 0, 0);
	return fb_make_value(r, type);
}

gb_internal fbValue fb_emit_cmp(fbBuilder *b, fbOp cmp_op, fbValue lhs, fbValue rhs) {
	GB_ASSERT(lhs.id != FB_NOREG);
	GB_ASSERT(rhs.id != FB_NOREG);
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
	GB_ASSERT(cond.id != FB_NOREG);
	GB_ASSERT(t.id != FB_NOREG);
	GB_ASSERT(f.id != FB_NOREG);
	fbType ft = fb_data_type(type);
	if (ft.kind == FBT_VOID) ft = FB_I64;
	u32 r = fb_inst_emit(b->proc, FB_SELECT, ft, cond.id, t.id, f.id, 0, 0);
	return fb_make_value(r, type);
}

gb_internal void fb_emit_memzero(fbBuilder *b, fbValue ptr, i64 size, i64 align) {
	GB_ASSERT(ptr.id != FB_NOREG);
	// Encoding: a=ptr, b=size_value, imm=alignment
	fbValue size_val = fb_emit_iconst(b, t_int, size);
	fb_inst_emit(b->proc, FB_MEMZERO, FB_VOID, ptr.id, size_val.id, FB_NOREG, 0, align);
}

gb_internal void fb_emit_memzero_v(fbBuilder *b, fbValue ptr, fbValue size, i64 align) {
	// Encoding: a=ptr, b=size_value, imm=alignment
	fb_inst_emit(b->proc, FB_MEMZERO, FB_VOID, ptr.id, size.id, FB_NOREG, 0, align);
}

gb_internal void fb_emit_memcpy(fbBuilder *b, fbValue dst, fbValue src, fbValue size, i64 align) {
	GB_ASSERT(dst.id != FB_NOREG);
	GB_ASSERT(src.id != FB_NOREG);
	GB_ASSERT(size.id != FB_NOREG);
	// Encoding: a=dst, b=src, c=size_value, imm=alignment
	fb_inst_emit(b->proc, FB_MEMCPY, FB_VOID, dst.id, src.id, size.id, 0, align);
}

gb_internal fbValue fb_emit_symaddr(fbBuilder *b, u32 sym_idx) {
	u32 r = fb_inst_emit(b->proc, FB_SYMADDR, FB_PTR, FB_NOREG, FB_NOREG, FB_NOREG, 0, cast(i64)sym_idx);
	return fb_make_value(r, nullptr);
}

gb_internal fbValue fb_emit_member(fbBuilder *b, fbValue base, i64 byte_offset) {
	GB_ASSERT(base.id != FB_NOREG);
	u32 r = fb_inst_emit(b->proc, FB_MEMBER, FB_PTR, base.id, FB_NOREG, FB_NOREG, 0, byte_offset);
	return fb_make_value(r, nullptr);
}

gb_internal fbValue fb_emit_array_access(fbBuilder *b, fbValue base, fbValue index, i64 stride) {
	GB_ASSERT(base.id != FB_NOREG);
	GB_ASSERT(index.id != FB_NOREG);
	u32 r = fb_inst_emit(b->proc, FB_ARRAY, FB_PTR, base.id, index.id, FB_NOREG, 0, stride);
	return fb_make_value(r, nullptr);
}

// Create a new block and return its id (does NOT switch to it)
gb_internal u32 fb_new_block(fbBuilder *b) {
	return fb_block_create(b->proc);
}

// Switch the insertion point to a block
gb_internal void fb_set_block(fbBuilder *b, u32 block_id) {
	GB_ASSERT(block_id < b->proc->block_count);
	fb_block_start(b->proc, block_id);
	b->current_block = block_id;
}

// Check if the current block has a terminator (JUMP/BRANCH/RET/UNREACHABLE)
gb_internal bool fb_block_is_terminated(fbBuilder *b) {
	fbProc *p = b->proc;
	GB_ASSERT(p->current_block < p->block_count);
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
				if (idx == nullptr) {
					// Lazily add proc not discovered during initial scan
					fbProc *p = fb_proc_create(b->module, e);
					u32 proc_idx = cast(u32)b->module->procs.count;
					array_add(&b->module->procs, p);
					map_set(&fb_entity_proc_map, e, proc_idx);
					idx = map_get(&fb_entity_proc_map, e);
				}
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

	case ExactValue_Compound: {
		// Compound constant (e.g. SIMD vector constant, struct literal).
		// Delegate to compound literal builder.
		Ast *node = value.value_compound;
		fbAddr addr = fb_build_compound_lit(b, node);
		return fb_addr_load(b, addr);
	}

	case ExactValue_Complex: {
		type = default_type(type);
		Type *ft = base_complex_elem_type(type);
		i64 elem_size = type_size_of(ft);

		fbAddr s = fb_add_local(b, type, nullptr, true);

		f64 real_val = value.value_complex->real;
		f64 imag_val = value.value_complex->imag;

		// Complex layout: {real, imag}
		fbValue real = fb_emit_fconst(b, ft, real_val);
		fb_emit_store(b, s.base, real);
		fbValue imag = fb_emit_fconst(b, ft, imag_val);
		fbValue imag_ptr = fb_emit_member(b, s.base, elem_size);
		fb_emit_store(b, imag_ptr, imag);

		s.base.type = type;
		return s.base;
	}

	case ExactValue_Quaternion: {
		type = default_type(type);
		Type *ft = base_complex_elem_type(type);
		i64 elem_size = type_size_of(ft);

		fbAddr s = fb_add_local(b, type, nullptr, true);

		// @QuaternionLayout: memory order = {imag_i, imag_j, imag_k, real_w}
		f64 imag_i = value.value_quaternion->imag;
		f64 imag_j = value.value_quaternion->jmag;
		f64 imag_k = value.value_quaternion->kmag;
		f64 real_w = value.value_quaternion->real;

		fb_emit_store(b, s.base, fb_emit_fconst(b, ft, imag_i));
		fb_emit_store(b, fb_emit_member(b, s.base, elem_size * 1), fb_emit_fconst(b, ft, imag_j));
		fb_emit_store(b, fb_emit_member(b, s.base, elem_size * 2), fb_emit_fconst(b, ft, imag_k));
		fb_emit_store(b, fb_emit_member(b, s.base, elem_size * 3), fb_emit_fconst(b, ft, real_w));

		s.base.type = type;
		return s.base;
	}

	case ExactValue_Typeid: {
		u64 id = type_hash_canonical_type(value.value_typeid);
		return fb_emit_iconst(b, type, cast(i64)id);
	}
	default:
		GB_PANIC("fb_const_value: unknown ExactValue kind %d", value.kind);
		return fb_value_nil();
	}
}

gb_internal fbAddr fb_add_local(fbBuilder *b, Type *type, Entity *entity, bool zero_init) {
	GB_ASSERT(type != nullptr);
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
	GB_ASSERT(addr.type != nullptr);
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
	if (addr.kind == fbAddr_BitField) {
		u32 bit_off = addr.bitfield.bit_offset;
		u32 bit_cnt = addr.bitfield.bit_count;
		u32 byte_off = bit_off / 8;
		u32 bit_shift = bit_off % 8;

		// Determine the load type: smallest integer type that covers the bits
		u32 bits_needed = bit_shift + bit_cnt;
		Type *load_type;
		if (bits_needed <= 8)  load_type = t_u8;
		else if (bits_needed <= 16) load_type = t_u16;
		else if (bits_needed <= 32) load_type = t_u32;
		else load_type = t_u64;

		fbValue ptr = addr.base;
		if (byte_off != 0) {
			ptr = fb_emit_member(b, ptr, byte_off);
		}
		fbValue raw = fb_emit_load(b, ptr, load_type);

		// Shift right to align the bit field
		if (bit_shift != 0) {
			fbValue shift = fb_emit_iconst(b, load_type, bit_shift);
			raw = fb_emit_arith(b, FB_LSHR, raw, shift, load_type);
		}

		// Mask to bit_cnt bits
		if (bit_cnt < 64) {
			i64 mask = (cast(i64)1 << bit_cnt) - 1;
			fbValue mask_val = fb_emit_iconst(b, load_type, mask);
			raw = fb_emit_arith(b, FB_AND, raw, mask_val, load_type);
		}

		// Sign extend if the field type is signed
		if (fb_type_is_signed(addr.type) && bit_cnt < cast(u32)(fb_type_size(fb_data_type(load_type)) * 8)) {
			i64 sign_bit = cast(i64)1 << (bit_cnt - 1);
			fbValue sb = fb_emit_iconst(b, load_type, sign_bit);
			raw = fb_emit_arith(b, FB_XOR, raw, sb, load_type);
			raw = fb_emit_arith(b, FB_SUB, raw, sb, load_type);
		}

		return fb_emit_conv(b, raw, addr.type);
	}

	if (addr.kind == fbAddr_Swizzle) {
		// Gather elements from the source array by swizzle indices into a new temp array.
		Type *result_type = addr.type;
		Type *array_type = base_type(result_type);
		GB_ASSERT(array_type->kind == Type_Array);
		Type *elem_type = array_type->Array.elem;
		i64 stride = type_size_of(elem_type);

		fbAddr res = fb_add_local(b, result_type, nullptr, false);
		for (u8 i = 0; i < addr.swizzle.count; i++) {
			u8 src_idx = addr.swizzle.indices[i];
			fbValue src_ptr = addr.base;
			if (src_idx > 0) src_ptr = fb_emit_member(b, addr.base, cast(i64)src_idx * stride);
			fbValue val = fb_emit_load(b, src_ptr, elem_type);

			fbValue dst_ptr = res.base;
			if (i > 0) dst_ptr = fb_emit_member(b, res.base, cast(i64)i * stride);
			fb_emit_store(b, dst_ptr, val);
		}

		fbType ft = fb_data_type(result_type);
		if (ft.kind != FBT_VOID) {
			return fb_emit_load(b, res.base, result_type);
		}
		fbValue ret = res.base;
		ret.type = result_type;
		return ret;
	}

	if (addr.kind == fbAddr_SwizzleLarge) {
		Type *result_type = addr.type;
		Type *array_type = base_type(result_type);
		GB_ASSERT(array_type->kind == Type_Array);
		Type *elem_type = array_type->Array.elem;
		i64 stride = type_size_of(elem_type);

		fbAddr res = fb_add_local(b, result_type, nullptr, false);
		for_array(i, addr.swizzle_large.indices) {
			i32 src_idx = addr.swizzle_large.indices[i];
			fbValue src_ptr = addr.base;
			if (src_idx > 0) src_ptr = fb_emit_member(b, addr.base, cast(i64)src_idx * stride);
			fbValue val = fb_emit_load(b, src_ptr, elem_type);

			fbValue dst_ptr = res.base;
			if (i > 0) dst_ptr = fb_emit_member(b, res.base, cast(i64)i * stride);
			fb_emit_store(b, dst_ptr, val);
		}

		fbType ft = fb_data_type(result_type);
		if (ft.kind != FBT_VOID) {
			return fb_emit_load(b, res.base, result_type);
		}
		fbValue ret = res.base;
		ret.type = result_type;
		return ret;
	}

	if (addr.kind == fbAddr_Map) {
		// Map lookup: call __dynamic_map_get, check for nil, copy value.
		Type *map_type = base_type(addr.map.map_type);
		GB_ASSERT(map_type->kind == Type_Map);

		Type *lookup_type = map_type->Map.lookup_result_type;
		fbAddr result = fb_add_local(b, lookup_type, nullptr, true);

		fbValue key_ptr = {};
		fbValue hash = fb_map_key_hash(b, addr.base, map_type, addr.map.key, &key_ptr);
		fbValue ptr = fb_dynamic_map_get(b, addr.base, map_type, hash, key_ptr);

		// ok = (ptr != nil)
		fbValue nil_val = fb_emit_iconst(b, t_rawptr, 0);
		nil_val.type = t_rawptr;
		fbValue ok = fb_emit_cmp(b, FB_CMP_NE, ptr, nil_val);

		// Store ok at field 1 of lookup result
		i64 ptr_size = b->module->target.ptr_size;
		Type *value_type = map_type->Map.value;
		i64 ok_offset = type_offset_of(lookup_type, 1);
		fbValue ok_ptr = fb_emit_member(b, result.base, ok_offset);
		fb_emit_store(b, ok_ptr, ok);

		// if ok, copy value from ptr to result field 0
		u32 then_blk = fb_new_block(b);
		u32 done_blk = fb_new_block(b);
		fb_emit_branch(b, ok, then_blk, done_blk);

		fb_set_block(b, then_blk);
		{
			fbValue val_ptr = ptr;
			val_ptr.type = alloc_type_pointer(value_type);
			fbType vft = fb_data_type(value_type);
			if (vft.kind != FBT_VOID) {
				fbValue val = fb_emit_load(b, val_ptr, value_type);
				fb_emit_store(b, result.base, val);
			} else {
				i64 vsz = type_size_of(value_type);
				i64 valign = type_align_of(value_type);
				if (vsz > 0) {
					fbValue sz = fb_emit_iconst(b, t_int, vsz);
					fb_emit_memcpy(b, result.base, val_ptr, sz, valign);
				}
			}
		}
		fb_emit_jump(b, done_blk);
		fb_set_block(b, done_blk);

		if (is_type_tuple(addr.map.result_type)) {
			return fb_addr_load(b, result);
		} else {
			// Single value: load field 0
			fbType vft = fb_data_type(map_type->Map.value);
			if (vft.kind != FBT_VOID) {
				return fb_emit_load(b, result.base, map_type->Map.value);
			}
			fbValue ret = result.base;
			ret.type = map_type->Map.value;
			return ret;
		}
	}

	GB_PANIC("TODO fb_addr_load kind=%d", addr.kind);
	return fb_value_nil();
}

gb_internal void fb_addr_store(fbBuilder *b, fbAddr addr, fbValue val) {
	if (addr.kind == fbAddr_Default) {
		GB_ASSERT(addr.base.id != FB_NOREG);
		fb_emit_copy_value(b, addr.base, val, addr.type);
		return;
	}

	if (addr.kind == fbAddr_BitField) {
		u32 bit_off = addr.bitfield.bit_offset;
		u32 bit_cnt = addr.bitfield.bit_count;
		u32 byte_off = bit_off / 8;
		u32 bit_shift = bit_off % 8;

		u32 bits_needed = bit_shift + bit_cnt;
		Type *store_type;
		if (bits_needed <= 8)  store_type = t_u8;
		else if (bits_needed <= 16) store_type = t_u16;
		else if (bits_needed <= 32) store_type = t_u32;
		else store_type = t_u64;

		// Convert the value to the storage integer type and mask to bit width
		fbValue new_val = fb_emit_conv(b, val, store_type);
		if (bit_cnt < 64) {
			i64 mask = (cast(i64)1 << bit_cnt) - 1;
			fbValue mask_val = fb_emit_iconst(b, store_type, mask);
			new_val = fb_emit_arith(b, FB_AND, new_val, mask_val, store_type);
		}

		// Shift into position
		if (bit_shift != 0) {
			fbValue shift = fb_emit_iconst(b, store_type, bit_shift);
			new_val = fb_emit_arith(b, FB_SHL, new_val, shift, store_type);
		}

		fbValue ptr = addr.base;
		if (byte_off != 0) {
			ptr = fb_emit_member(b, ptr, byte_off);
		}

		// Read-modify-write: clear target bits, OR in new bits
		fbValue old_val = fb_emit_load(b, ptr, store_type);
		i64 clear_mask = ~(((cast(i64)1 << bit_cnt) - 1) << bit_shift);
		fbValue cmask = fb_emit_iconst(b, store_type, clear_mask);
		fbValue cleared = fb_emit_arith(b, FB_AND, old_val, cmask, store_type);
		fbValue merged = fb_emit_arith(b, FB_OR, cleared, new_val, store_type);
		fb_emit_store(b, ptr, merged);
		return;
	}

	if (addr.kind == fbAddr_Swizzle) {
		// Scatter-write: decompose the source value into elements and store
		// each at the swizzle-mapped position in the destination array.
		Type *result_type = addr.type;
		Type *array_type = base_type(result_type);
		GB_ASSERT(array_type->kind == Type_Array);
		Type *elem_type = array_type->Array.elem;
		i64 stride = type_size_of(elem_type);

		// val is either a scalar (if swizzle produces a scalar) or an aggregate pointer
		for (u8 i = 0; i < addr.swizzle.count; i++) {
			u8 dst_idx = addr.swizzle.indices[i];
			fbValue src_ptr = val;
			if (i > 0) src_ptr = fb_emit_member(b, val, cast(i64)i * stride);
			fbValue elem_val = fb_emit_load(b, src_ptr, elem_type);

			fbValue dst_ptr = addr.base;
			if (dst_idx > 0) dst_ptr = fb_emit_member(b, addr.base, cast(i64)dst_idx * stride);
			fb_emit_store(b, dst_ptr, elem_val);
		}
		return;
	}

	if (addr.kind == fbAddr_SwizzleLarge) {
		Type *result_type = addr.type;
		Type *array_type = base_type(result_type);
		GB_ASSERT(array_type->kind == Type_Array);
		Type *elem_type = array_type->Array.elem;
		i64 stride = type_size_of(elem_type);

		for_array(i, addr.swizzle_large.indices) {
			i32 dst_idx = addr.swizzle_large.indices[i];
			fbValue src_ptr = val;
			if (i > 0) src_ptr = fb_emit_member(b, val, cast(i64)i * stride);
			fbValue elem_val = fb_emit_load(b, src_ptr, elem_type);

			fbValue dst_ptr = addr.base;
			if (dst_idx > 0) dst_ptr = fb_emit_member(b, addr.base, cast(i64)dst_idx * stride);
			fb_emit_store(b, dst_ptr, elem_val);
		}
		return;
	}

	if (addr.kind == fbAddr_Map) {
		// Map store: m[key] = val → call __dynamic_map_set
		Type *map_type = base_type(addr.map.map_type);
		Type *value_type = map_type->Map.value;

		// Store value to a local and take its address
		fbAddr val_local = fb_add_local(b, value_type, nullptr, false);
		fb_emit_copy_value(b, val_local.base, val, value_type);
		fbValue val_ptr = val_local.base;
		val_ptr.type = t_rawptr;

		fbValue key_ptr = {};
		fbValue hash = fb_map_key_hash(b, addr.base, map_type, addr.map.key, &key_ptr);
		fb_dynamic_map_set(b, addr.base, map_type, hash, key_ptr, val_ptr, nullptr);
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
	p->sret_slot_idx = -1;

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

// ── Map support ───────────────────────────────────────────────────────
//
// Maps use the dynamic runtime calls: __dynamic_map_get, __dynamic_map_set,
// __dynamic_map_reserve. Each map type needs Map_Cell_Info and Map_Info
// globals, plus synthesized hasher and equal procs for the key type.

// Look up a runtime proc entity by name and return its proc index.
// If the proc wasn't discovered during initial scanning (e.g. because
// min_dep_count == 0), lazily create it now.
gb_internal u32 fb_lookup_runtime_proc(fbModule *m, String name) {
	Entity *e = scope_lookup_current(m->info->runtime_package->scope, name);
	GB_ASSERT_MSG(e != nullptr, "runtime proc '%.*s' not found", LIT(name));
	u32 *idx = map_get(&fb_entity_proc_map, e);
	if (idx != nullptr) {
		return *idx;
	}

	// Lazily create the proc — this happens for runtime procs that have
	// min_dep_count == 0 because user code doesn't reference them directly,
	// only the backend's synthesized code does (e.g. __dynamic_map_set).
	fbProc *p = fb_proc_create(m, e);
	u32 proc_idx = cast(u32)m->procs.count;
	array_add(&m->procs, p);
	map_set(&fb_entity_proc_map, e, proc_idx);
	return proc_idx;
}

// Emit a call to a contextless proc: proc "contextless" (args...) -> ret_type
gb_internal fbValue fb_emit_call_contextless(fbBuilder *b, u32 proc_idx, fbValue *args, u32 arg_count, Type *ret_type) {
	fbValue target = fb_emit_symaddr(b, proc_idx);
	u32 aux_start = b->proc->aux_count;
	for (u32 i = 0; i < arg_count; i++) {
		fb_aux_push(b->proc, args[i].id);
	}
	u32 arg_total = b->proc->aux_count - aux_start;
	fbType ret_ft = (ret_type != nullptr) ? fb_data_type(ret_type) : FB_VOID;
	u32 r = fb_inst_emit(b->proc, FB_CALL, ret_ft, target.id, aux_start, arg_total, 0, 0);
	// Contextless uses Odin CC (no context pointer)
	fbInst *inst = &b->proc->insts[b->proc->inst_count - 1];
	inst->flags = FBCC_ODIN;
	return fb_make_value(r, ret_type);
}

// Emit a call to an Odin-CC proc, passing context as last arg.
gb_internal fbValue fb_emit_call_odin(fbBuilder *b, u32 proc_idx, fbValue *args, u32 arg_count, Type *ret_type) {
	fbValue target = fb_emit_symaddr(b, proc_idx);
	u32 aux_start = b->proc->aux_count;
	for (u32 i = 0; i < arg_count; i++) {
		fb_aux_push(b->proc, args[i].id);
	}
	// Context pointer (Odin CC, always last)
	if (b->context_stack.count == 0) {
		fbAddr ctx_addr = fb_add_local(b, t_context, nullptr, true);
		fbContextData *cd = array_add_and_get(&b->context_stack);
		cd->ctx = ctx_addr;
		cd->uses_default = false;
	}
	fbContextData *ctx = &b->context_stack[b->context_stack.count - 1];
	fbValue ctx_ptr = fb_addr_load(b, ctx->ctx);
	fb_aux_push(b->proc, ctx_ptr.id);

	u32 arg_total = b->proc->aux_count - aux_start;
	fbType ret_ft = (ret_type != nullptr) ? fb_data_type(ret_type) : FB_VOID;
	u32 r = fb_inst_emit(b->proc, FB_CALL, ret_ft, target.id, aux_start, arg_total, 0, 0);
	fbInst *inst = &b->proc->insts[b->proc->inst_count - 1];
	inst->flags = FBCC_ODIN;
	return fb_make_value(r, ret_type);
}

// Generate a Map_Cell_Info global for a given element type. Returns global_entries index.
gb_internal u32 fb_gen_map_cell_info(fbModule *m, Type *type) {
	u32 *found = map_get(&m->map_cell_info_map, type);
	if (found) return *found;

	i64 size = 0, len = 0;
	map_cell_size_and_len(type, &size, &len);

	i64 ptr_size = m->target.ptr_size;
	u32 global_size = cast(u32)(4 * ptr_size);  // 4 uintptr fields
	u8 *buf = gb_alloc_array(heap_allocator(), u8, global_size);
	gb_zero_size(buf, global_size);

	// Map_Cell_Info = {size_of_type, align_of_type, size_of_cell, elements_per_cell}
	i64 esz = type_size_of(type);
	i64 eal = type_align_of(type);
	gb_memmove(buf + 0 * ptr_size, &esz, ptr_size);
	gb_memmove(buf + 1 * ptr_size, &eal, ptr_size);
	gb_memmove(buf + 2 * ptr_size, &size, ptr_size);
	gb_memmove(buf + 3 * ptr_size, &len, ptr_size);

	fbGlobalEntry ge = {};
	ge.name = str_lit("__$fb_map_cell_info");
	ge.odin_type = t_map_cell_info;
	ge.init_data = buf;
	ge.size = global_size;
	ge.align = cast(u32)ptr_size;
	ge.is_foreign = false;
	ge.is_export = false;

	u32 gidx = cast(u32)m->global_entries.count;
	array_add(&m->global_entries, ge);
	map_set(&m->map_cell_info_map, type, gidx);
	return gidx;
}

// Generate (or look up) a hasher proc for a key type.
// Signature: proc "contextless" (data: rawptr, seed: uintptr) -> uintptr
// For simple-compare types, calls default_hasher(data, seed, sizeof(type)).
// For strings, calls default_hasher_string(data, seed).
gb_internal u32 fb_gen_hasher_proc(fbBuilder *b, Type *type) {
	type = core_type(type);
	fbModule *m = b->module;
	u32 *found = map_get(&m->map_hasher_procs, type);
	if (found) return *found;

	// Synthesize a minimal fbProc that wraps a runtime hasher call.
	// The proc is contextless(rawptr, uintptr) -> uintptr, so it takes
	// 2 GP args (RDI=data, RSI=seed), returns 1 GP (RAX).
	//
	// For simple-compare types: call default_hasher(data, seed, sizeof(type))
	// For strings: call default_hasher_string(data, seed)
	// For cstrings: call default_hasher_cstring(data, seed)
	// For floats: load value, convert to f64, call default_hasher_f64(f64_val, seed)
	//
	// We generate these as regular IR-based procs by building instructions manually.

	fbProc *p = gb_alloc_item(permanent_allocator(), fbProc);
	gb_zero_item(p);
	p->name = str_lit("__$fb_hasher");
	p->is_foreign = false;
	p->is_export = false;
	p->current_block = FB_NOREG;
	p->split_returns_index = -1;
	p->sret_slot_idx = -1;

	p->inst_cap  = 32;
	p->insts     = gb_alloc_array(heap_allocator(), fbInst, p->inst_cap);
	p->block_cap = 2;
	p->blocks    = gb_alloc_array(heap_allocator(), fbBlock, p->block_cap);
	p->slot_cap  = 4;
	p->slots     = gb_alloc_array(heap_allocator(), fbStackSlot, p->slot_cap);
	p->aux_cap   = 16;
	p->aux       = gb_alloc_array(heap_allocator(), u32, p->aux_cap);
	p->loc_cap   = 2;
	p->locs      = gb_alloc_array(heap_allocator(), fbLoc, p->loc_cap);

	// Set up 2 params: data(rawptr), seed(uintptr)
	p->param_count = 2;
	p->param_locs = gb_alloc_array(heap_allocator(), fbProc::fbParamLoc, 2);

	// Slot 0: data (rawptr, 8 bytes)
	u32 slot0 = fb_slot_create(p, 8, 8, nullptr, t_rawptr);
	p->param_locs[0] = {slot0, 0};

	// Slot 1: seed (uintptr, 8 bytes)
	u32 slot1 = fb_slot_create(p, 8, 8, nullptr, t_uintptr);
	p->param_locs[1] = {slot1, 0};

	u32 entry = fb_block_create(p);
	fb_block_start(p, entry);

	// Load params from slots
	u32 data_ptr_id = fb_inst_emit(p, FB_LOAD, {FBT_PTR, 0}, fb_inst_emit(p, FB_ALLOCA, {FBT_PTR, 0}, slot0, 0, 0, 0, 0), 0, 0, 0, 8);
	u32 seed_id     = fb_inst_emit(p, FB_LOAD, {FBT_I64, 0}, fb_inst_emit(p, FB_ALLOCA, {FBT_PTR, 0}, slot1, 0, 0, 0, 0), 0, 0, 0, 8);

	u32 proc_idx = cast(u32)m->procs.count;
	array_add(&m->procs, p);
	map_set(&m->map_hasher_procs, type, proc_idx);

	if (is_type_string(type)) {
		// Call default_hasher_string(data, seed) -> uintptr
		u32 target_idx = fb_lookup_runtime_proc(m, str_lit("default_hasher_string"));
		u32 target_id = fb_inst_emit(p, FB_SYMADDR, {FBT_PTR, 0}, FB_NOREG, 0, 0, 0, cast(i64)target_idx);
		fb_aux_push(p, data_ptr_id);
		fb_aux_push(p, seed_id);
		u32 result = fb_inst_emit(p, FB_CALL, {FBT_I64, 0}, target_id, p->aux_count - 2, 2, 0, 0);
		p->insts[p->inst_count - 1].flags = FBCC_ODIN;
		fb_inst_emit(p, FB_RET, FB_VOID, result, FB_NOREG, FB_NOREG, 0, 0);
	} else if (is_type_cstring(type)) {
		u32 target_idx = fb_lookup_runtime_proc(m, str_lit("default_hasher_cstring"));
		u32 target_id = fb_inst_emit(p, FB_SYMADDR, {FBT_PTR, 0}, FB_NOREG, 0, 0, 0, cast(i64)target_idx);
		fb_aux_push(p, data_ptr_id);
		fb_aux_push(p, seed_id);
		u32 result = fb_inst_emit(p, FB_CALL, {FBT_I64, 0}, target_id, p->aux_count - 2, 2, 0, 0);
		p->insts[p->inst_count - 1].flags = FBCC_ODIN;
		fb_inst_emit(p, FB_RET, FB_VOID, result, FB_NOREG, FB_NOREG, 0, 0);
	} else {
		// Simple-compare or anything else: call default_hasher(data, seed, sizeof(type))
		u32 target_idx = fb_lookup_runtime_proc(m, str_lit("default_hasher"));
		u32 target_id = fb_inst_emit(p, FB_SYMADDR, {FBT_PTR, 0}, FB_NOREG, 0, 0, 0, cast(i64)target_idx);
		u32 size_id = fb_inst_emit(p, FB_ICONST, {FBT_I64, 0}, FB_NOREG, 0, 0, 0, type_size_of(type));
		fb_aux_push(p, data_ptr_id);
		fb_aux_push(p, seed_id);
		fb_aux_push(p, size_id);
		u32 result = fb_inst_emit(p, FB_CALL, {FBT_I64, 0}, target_id, p->aux_count - 3, 3, 0, 0);
		p->insts[p->inst_count - 1].flags = FBCC_ODIN;
		fb_inst_emit(p, FB_RET, FB_VOID, result, FB_NOREG, FB_NOREG, 0, 0);
	}

	return proc_idx;
}

// Generate (or look up) an equal proc for a key type.
// Signature: proc "contextless" (a: rawptr, b: rawptr) -> bool
gb_internal u32 fb_gen_equal_proc(fbBuilder *b, Type *type) {
	type = core_type(type);
	fbModule *m = b->module;
	u32 *found = map_get(&m->map_equal_procs, type);
	if (found) return *found;

	fbProc *p = gb_alloc_item(permanent_allocator(), fbProc);
	gb_zero_item(p);
	p->name = str_lit("__$fb_equal");
	p->is_foreign = false;
	p->is_export = false;
	p->current_block = FB_NOREG;
	p->split_returns_index = -1;
	p->sret_slot_idx = -1;

	p->inst_cap  = 32;
	p->insts     = gb_alloc_array(heap_allocator(), fbInst, p->inst_cap);
	p->block_cap = 4;
	p->blocks    = gb_alloc_array(heap_allocator(), fbBlock, p->block_cap);
	p->slot_cap  = 4;
	p->slots     = gb_alloc_array(heap_allocator(), fbStackSlot, p->slot_cap);
	p->aux_cap   = 16;
	p->aux       = gb_alloc_array(heap_allocator(), u32, p->aux_cap);
	p->loc_cap   = 2;
	p->locs      = gb_alloc_array(heap_allocator(), fbLoc, p->loc_cap);

	// 2 params: a(rawptr), b(rawptr)
	p->param_count = 2;
	p->param_locs = gb_alloc_array(heap_allocator(), fbProc::fbParamLoc, 2);

	u32 slot0 = fb_slot_create(p, 8, 8, nullptr, t_rawptr);
	p->param_locs[0] = {slot0, 0};
	u32 slot1 = fb_slot_create(p, 8, 8, nullptr, t_rawptr);
	p->param_locs[1] = {slot1, 0};

	u32 entry = fb_block_create(p);
	fb_block_start(p, entry);

	u32 a_id = fb_inst_emit(p, FB_LOAD, {FBT_PTR, 0}, fb_inst_emit(p, FB_ALLOCA, {FBT_PTR, 0}, slot0, 0, 0, 0, 0), 0, 0, 0, 8);
	u32 b_id = fb_inst_emit(p, FB_LOAD, {FBT_PTR, 0}, fb_inst_emit(p, FB_ALLOCA, {FBT_PTR, 0}, slot1, 0, 0, 0, 0), 0, 0, 0, 8);

	u32 proc_idx = cast(u32)m->procs.count;
	array_add(&m->procs, p);
	map_set(&m->map_equal_procs, type, proc_idx);

	i64 sz = type_size_of(type);

	if (is_type_string(type)) {
		// String equal: compare len, then memcmp data
		// Load a.len, b.len
		u32 a_len = fb_inst_emit(p, FB_LOAD, {FBT_I64, 0}, fb_inst_emit(p, FB_MEMBER, {FBT_PTR, 0}, a_id, 0, 0, 0, 8), 0, 0, 0, 8);
		u32 b_len = fb_inst_emit(p, FB_LOAD, {FBT_I64, 0}, fb_inst_emit(p, FB_MEMBER, {FBT_PTR, 0}, b_id, 0, 0, 0, 8), 0, 0, 0, 8);
		u32 len_eq = fb_inst_emit(p, FB_CMP_EQ, {FBT_I1, 0}, a_len, b_len, 0, 0, 0);

		u32 then_blk = fb_block_create(p);
		u32 done_blk = fb_block_create(p);
		fb_inst_emit(p, FB_BRANCH, FB_VOID, len_eq, then_blk, done_blk, 0, 0);

		// then: memcmp data pointers
		fb_block_start(p, then_blk);
		u32 a_data = fb_inst_emit(p, FB_LOAD, {FBT_PTR, 0}, a_id, 0, 0, 0, 8);
		u32 b_data = fb_inst_emit(p, FB_LOAD, {FBT_PTR, 0}, b_id, 0, 0, 0, 8);
		u32 memcmp_idx = fb_ensure_c_proc(m, str_lit("memcmp"));
		u32 memcmp_sym = fb_inst_emit(p, FB_SYMADDR, {FBT_PTR, 0}, FB_NOREG, 0, 0, 0, cast(i64)memcmp_idx);
		fb_aux_push(p, a_data);
		fb_aux_push(p, b_data);
		fb_aux_push(p, a_len);
		u32 cmp_result = fb_inst_emit(p, FB_CALL, {FBT_I32, 0}, memcmp_sym, p->aux_count - 3, 3, 0, 0);
		p->insts[p->inst_count - 1].flags = FBCC_C;
		u32 zero32 = fb_inst_emit(p, FB_ICONST, {FBT_I32, 0}, FB_NOREG, 0, 0, 0, 0);
		u32 bytes_eq = fb_inst_emit(p, FB_CMP_EQ, {FBT_I1, 0}, cmp_result, zero32, 0, 0, 0);
		fb_inst_emit(p, FB_RET, FB_VOID, bytes_eq, FB_NOREG, FB_NOREG, 0, 0);

		// done: return false (len mismatch)
		fb_block_start(p, done_blk);
		u32 false_val = fb_inst_emit(p, FB_ICONST, {FBT_I1, 0}, FB_NOREG, 0, 0, 0, 0);
		fb_inst_emit(p, FB_RET, FB_VOID, false_val, FB_NOREG, FB_NOREG, 0, 0);
	} else {
		// Simple memcmp for simple-compare types (integers, pointers, etc.)
		u32 memcmp_idx = fb_ensure_c_proc(m, str_lit("memcmp"));
		u32 memcmp_sym = fb_inst_emit(p, FB_SYMADDR, {FBT_PTR, 0}, FB_NOREG, 0, 0, 0, cast(i64)memcmp_idx);
		u32 size_id = fb_inst_emit(p, FB_ICONST, {FBT_I64, 0}, FB_NOREG, 0, 0, 0, sz);
		fb_aux_push(p, a_id);
		fb_aux_push(p, b_id);
		fb_aux_push(p, size_id);
		u32 cmp_result = fb_inst_emit(p, FB_CALL, {FBT_I32, 0}, memcmp_sym, p->aux_count - 3, 3, 0, 0);
		p->insts[p->inst_count - 1].flags = FBCC_C;
		u32 zero32 = fb_inst_emit(p, FB_ICONST, {FBT_I32, 0}, FB_NOREG, 0, 0, 0, 0);
		u32 eq = fb_inst_emit(p, FB_CMP_EQ, {FBT_I1, 0}, cmp_result, zero32, 0, 0, 0);
		fb_inst_emit(p, FB_RET, FB_VOID, eq, FB_NOREG, FB_NOREG, 0, 0);
	}

	return proc_idx;
}

// Generate a Map_Info global for a map type. Returns global_entries index.
// Map_Info = {ks: ^Map_Cell_Info, vs: ^Map_Cell_Info, key_hasher: proc, key_equal: proc}
gb_internal u32 fb_gen_map_info(fbBuilder *b, Type *map_type) {
	map_type = base_type(map_type);
	GB_ASSERT(map_type->kind == Type_Map);

	fbModule *m = b->module;
	u32 *found = map_get(&m->map_info_map, map_type);
	if (found) return *found;

	u32 ks_gidx = fb_gen_map_cell_info(m, map_type->Map.key);
	u32 vs_gidx = fb_gen_map_cell_info(m, map_type->Map.value);
	u32 hasher_idx = fb_gen_hasher_proc(b, map_type->Map.key);
	u32 equal_idx  = fb_gen_equal_proc(b, map_type->Map.key);

	i64 ptr_size = m->target.ptr_size;
	u32 global_size = cast(u32)(4 * ptr_size);  // 4 pointers
	u8 *buf = gb_alloc_array(heap_allocator(), u8, global_size);
	gb_zero_size(buf, global_size);

	fbGlobalEntry ge = {};
	ge.name = str_lit("__$fb_map_info");
	ge.odin_type = t_map_info;
	ge.init_data = buf;
	ge.size = global_size;
	ge.align = cast(u32)ptr_size;
	ge.is_foreign = false;
	ge.is_export = false;

	u32 gidx = cast(u32)m->global_entries.count;
	array_add(&m->global_entries, ge);
	map_set(&m->map_info_map, map_type, gidx);

	// Data relocations for the 4 pointers:
	// [0] ks → &map_cell_info_global for key type
	fbDataReloc r0 = {};
	r0.global_idx = gidx;
	r0.local_offset = 0;
	r0.target_sym = FB_GLOBAL_SYM_BASE + ks_gidx;
	r0.addend = 0;
	array_add(&m->data_relocs, r0);

	// [1] vs → &map_cell_info_global for value type
	fbDataReloc r1 = {};
	r1.global_idx = gidx;
	r1.local_offset = cast(u32)ptr_size;
	r1.target_sym = FB_GLOBAL_SYM_BASE + vs_gidx;
	r1.addend = 0;
	array_add(&m->data_relocs, r1);

	// [2] key_hasher → hasher proc
	fbDataReloc r2 = {};
	r2.global_idx = gidx;
	r2.local_offset = cast(u32)(2 * ptr_size);
	r2.target_sym = hasher_idx;  // proc symbol
	r2.addend = 0;
	array_add(&m->data_relocs, r2);

	// [3] key_equal → equal proc
	fbDataReloc r3 = {};
	r3.global_idx = gidx;
	r3.local_offset = cast(u32)(3 * ptr_size);
	r3.target_sym = equal_idx;  // proc symbol
	r3.addend = 0;
	array_add(&m->data_relocs, r3);

	return gidx;
}

// Get ^Map_Info pointer as an fbValue (pointer to the Map_Info global).
gb_internal fbValue fb_map_info_ptr(fbBuilder *b, Type *map_type) {
	u32 gidx = fb_gen_map_info(b, map_type);
	u32 sym = FB_GLOBAL_SYM_BASE + gidx;
	fbValue ptr = fb_emit_symaddr(b, sym);
	ptr.type = t_map_info_ptr;
	return ptr;
}

// Inline map_seed_from_map_data as SplitMix64:
//   mix = data + 0x9e3779b97f4a7c15
//   mix = (mix ^ (mix >> 30)) * 0xbf58476d1ce4e5b9
//   mix = (mix ^ (mix >> 27)) * 0x94d049bb133111eb
//   return mix ^ (mix >> 31)
gb_internal fbValue fb_map_seed(fbBuilder *b, fbValue data_uintptr) {
	fbValue c1 = fb_emit_iconst(b, t_uintptr, 0x9e3779b97f4a7c15LL);
	fbValue mix = fb_emit_arith(b, FB_ADD, data_uintptr, c1, t_uintptr);

	fbValue s30 = fb_emit_iconst(b, t_uintptr, 30);
	fbValue t1 = fb_emit_arith(b, FB_LSHR, mix, s30, t_uintptr);
	mix = fb_emit_arith(b, FB_XOR, mix, t1, t_uintptr);
	fbValue c2 = fb_emit_iconst(b, t_uintptr, cast(i64)0xbf58476d1ce4e5b9ULL);
	mix = fb_emit_arith(b, FB_MUL, mix, c2, t_uintptr);

	fbValue s27 = fb_emit_iconst(b, t_uintptr, 27);
	fbValue t2 = fb_emit_arith(b, FB_LSHR, mix, s27, t_uintptr);
	mix = fb_emit_arith(b, FB_XOR, mix, t2, t_uintptr);
	fbValue c3 = fb_emit_iconst(b, t_uintptr, cast(i64)0x94d049bb133111ebULL);
	mix = fb_emit_arith(b, FB_MUL, mix, c3, t_uintptr);

	fbValue s31 = fb_emit_iconst(b, t_uintptr, 31);
	fbValue t3 = fb_emit_arith(b, FB_LSHR, mix, s31, t_uintptr);
	mix = fb_emit_arith(b, FB_XOR, mix, t3, t_uintptr);
	return mix;
}

// Extract the data pointer from a Raw_Map value (mask off lower 6 bits).
gb_internal fbValue fb_map_data_uintptr(fbBuilder *b, fbValue map_data_field) {
	fbValue mask = fb_emit_iconst(b, t_uintptr, ~cast(i64)0x3F);
	return fb_emit_arith(b, FB_AND, map_data_field, mask, t_uintptr);
}

// Compute map capacity from data field: cap = (data == 0) ? 0 : (1 << (data & 0x3F))
gb_internal fbValue fb_map_cap(fbBuilder *b, fbValue map_data_field) {
	fbValue zero = fb_emit_iconst(b, t_uintptr, 0);
	fbValue one  = fb_emit_iconst(b, t_uintptr, 1);
	fbValue mask = fb_emit_iconst(b, t_uintptr, 0x3F);
	fbValue log2_cap = fb_emit_arith(b, FB_AND, map_data_field, mask, t_uintptr);
	fbValue cap = fb_emit_arith(b, FB_SHL, one, log2_cap, t_uintptr);
	fbValue is_zero = fb_emit_cmp(b, FB_CMP_EQ, map_data_field, zero);
	return fb_emit_select(b, is_zero, zero, cap, t_uintptr);
}

// Index into a map cell array accounting for cache-line padding.
// cell_index_static(type, base_ptr, index) -> pointer to element
gb_internal fbValue fb_map_cell_index(fbBuilder *b, Type *type, fbValue cells_ptr, fbValue index) {
	i64 elem_sz = type_size_of(type);
	i64 size = 0, len = 0;
	map_cell_size_and_len(type, &size, &len);

	index = fb_emit_conv(b, index, t_uintptr);

	if (size == len * elem_sz) {
		// No padding — simple array index
		return fb_emit_array_access(b, cells_ptr, index, elem_sz);
	}

	// With padding: cell_idx = index / len, data_idx = index % len
	// Offset = cell_idx * size + data_idx * elem_sz
	fbValue cell_idx, data_idx;
	fbValue size_const = fb_emit_iconst(b, t_uintptr, size);
	fbValue len_const  = fb_emit_iconst(b, t_uintptr, len);

	if (is_power_of_two(cast(u64)len)) {
		u64 log2_len = floor_log2(cast(u64)len);
		if (log2_len == 0) {
			cell_idx = index;
		} else {
			fbValue shift = fb_emit_iconst(b, t_uintptr, cast(i64)log2_len);
			cell_idx = fb_emit_arith(b, FB_LSHR, index, shift, t_uintptr);
		}
		fbValue and_mask = fb_emit_iconst(b, t_uintptr, len - 1);
		data_idx = fb_emit_arith(b, FB_AND, index, and_mask, t_uintptr);
	} else {
		cell_idx = fb_emit_arith(b, FB_UDIV, index, len_const, t_uintptr);
		data_idx = fb_emit_arith(b, FB_UMOD, index, len_const, t_uintptr);
	}

	fbValue cell_offset = fb_emit_arith(b, FB_MUL, size_const, cell_idx, t_uintptr);
	fbValue elem_offset = fb_emit_arith(b, FB_MUL, fb_emit_iconst(b, t_uintptr, elem_sz), data_idx, t_uintptr);
	fbValue total = fb_emit_arith(b, FB_ADD, cell_offset, elem_offset, t_uintptr);

	// Base is uintptr, add offset and convert back to pointer
	fbValue base_int = fb_emit_conv(b, cells_ptr, t_uintptr);
	fbValue result_int = fb_emit_arith(b, FB_ADD, base_int, total, t_uintptr);
	fbValue result = fb_emit_conv(b, result_int, t_rawptr);
	result.type = alloc_type_pointer(type);
	return result;
}

// Check if a map hash value is valid: (hash != 0) & ((hash >> 63) == 0)
gb_internal fbValue fb_map_hash_is_valid(fbBuilder *b, fbValue hash) {
	fbValue zero = fb_emit_iconst(b, t_uintptr, 0);
	fbValue not_empty = fb_emit_cmp(b, FB_CMP_NE, hash, zero);
	fbValue shift = fb_emit_iconst(b, t_uintptr, 63);
	fbValue top = fb_emit_arith(b, FB_LSHR, hash, shift, t_uintptr);
	fbValue not_deleted = fb_emit_cmp(b, FB_CMP_EQ, top, zero);
	return fb_emit_arith(b, FB_AND, not_empty, not_deleted, t_bool);
}

// Hash a key value for a map operation.
// Returns the hash and sets *key_ptr_out to a rawptr to the key.
gb_internal fbValue fb_map_key_hash(fbBuilder *b, fbValue map_ptr, Type *map_type, fbValue key, fbValue *key_ptr_out) {
	Type *key_type = base_type(map_type)->Map.key;

	// Store key to a local and take its address
	fbAddr key_local = fb_add_local(b, key_type, nullptr, false);
	fb_emit_copy_value(b, key_local.base, key, key_type);
	fbValue key_ptr = key_local.base;
	key_ptr.type = t_rawptr;
	if (key_ptr_out) *key_ptr_out = key_ptr;

	// Get seed: load map.data (field 0), apply SplitMix64
	fbValue map_val_data = fb_emit_load(b, map_ptr, t_uintptr);
	fbValue data_clean = fb_map_data_uintptr(b, map_val_data);
	fbValue seed = fb_map_seed(b, data_clean);

	// Call hasher proc
	u32 hasher_idx = fb_gen_hasher_proc(b, key_type);
	fbValue args[2] = { key_ptr, seed };
	return fb_emit_call_contextless(b, hasher_idx, args, 2, t_uintptr);
}

// Call __dynamic_map_get(map_ptr, map_info, hash, key_ptr) -> rawptr
gb_internal fbValue fb_dynamic_map_get(fbBuilder *b, fbValue map_ptr, Type *map_type, fbValue hash, fbValue key_ptr) {
	u32 proc_idx = fb_lookup_runtime_proc(b->module, str_lit("__dynamic_map_get"));
	fbValue info_ptr = fb_map_info_ptr(b, map_type);
	fbValue args[4] = {
		fb_emit_conv(b, map_ptr, t_rawptr),  // ^Raw_Map
		info_ptr,                              // ^Map_Info
		hash,                                  // Map_Hash
		key_ptr,                               // rawptr to key
	};
	return fb_emit_call_contextless(b, proc_idx, args, 4, t_rawptr);
}

// Call __dynamic_map_set(map_ptr, map_info, hash, key_ptr, val_ptr, loc) -> rawptr
gb_internal void fb_dynamic_map_set(fbBuilder *b, fbValue map_ptr, Type *map_type, fbValue hash, fbValue key_ptr, fbValue val_ptr, Ast *node) {
	u32 proc_idx = fb_lookup_runtime_proc(b->module, str_lit("__dynamic_map_set"));
	fbValue info_ptr = fb_map_info_ptr(b, map_type);

	// Build source code location for the loc parameter
	String proc_name = {};
	if (b->entity != nullptr) {
		proc_name = b->entity->token.string;
	}
	TokenPos pos = {};
	if (node != nullptr) {
		pos = ast_token(node).pos;
	}
	fbValue loc = fb_build_source_code_location(b, proc_name, pos);

	fbValue args[6] = {
		fb_emit_conv(b, map_ptr, t_rawptr),  // ^Raw_Map
		info_ptr,                              // ^Map_Info
		hash,                                  // Map_Hash
		fb_emit_conv(b, key_ptr, t_rawptr),   // key rawptr
		fb_emit_conv(b, val_ptr, t_rawptr),   // value rawptr
		loc,                                   // Source_Code_Location
	};
	fb_emit_call_odin(b, proc_idx, args, 6, t_rawptr);
}

// Call __dynamic_map_reserve(map_ptr, map_info, capacity, loc) -> Allocator_Error
gb_internal void fb_dynamic_map_reserve(fbBuilder *b, fbValue map_ptr, Type *map_type, fbValue capacity, Ast *node) {
	u32 proc_idx = fb_lookup_runtime_proc(b->module, str_lit("__dynamic_map_reserve"));
	fbValue info_ptr = fb_map_info_ptr(b, map_type);

	String proc_name = {};
	if (b->entity != nullptr) proc_name = b->entity->token.string;
	TokenPos pos = {};
	if (node != nullptr) pos = ast_token(node).pos;
	fbValue loc = fb_build_source_code_location(b, proc_name, pos);

	fbValue args[4] = {
		fb_emit_conv(b, map_ptr, t_rawptr),
		info_ptr,
		fb_emit_conv(b, capacity, t_uint),
		loc,
	};
	fb_emit_call_odin(b, proc_idx, args, 4, nullptr);
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

		if (se->swizzle_count > 0) {
			u8 swizzle_count = se->swizzle_count;
			u8 swizzle_indices_raw = se->swizzle_indices;
			u8 indices[4] = {};
			for (u8 i = 0; i < swizzle_count; i++) {
				indices[i] = (swizzle_indices_raw >> (i * 2)) & 3;
			}

			fbAddr base_addr = fb_build_addr(b, se->expr);

			Type *result_type = type_of_expr(expr);
			fbAddr addr = {};
			addr.kind = fbAddr_Swizzle;
			addr.base = base_addr.base;
			addr.type = result_type;
			addr.swizzle.count = swizzle_count;
			addr.swizzle.indices[0] = indices[0];
			addr.swizzle.indices[1] = indices[1];
			addr.swizzle.indices[2] = indices[2];
			addr.swizzle.indices[3] = indices[3];
			return addr;
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

		if (sel.is_bit_field) {
			// Bit field access: the base pointer points to the containing
			// backing storage. Store bit offset and size for load/store.
			Type *parent_type = base_type(type_of_expr(se->expr));
			GB_ASSERT(parent_type->kind == Type_BitField);
			GB_ASSERT(sel.index.count == 1);
			i32 field_idx = sel.index[0];
			i64 bit_offset = parent_type->BitField.bit_offsets[field_idx];
			i64 bit_size   = parent_type->BitField.bit_sizes[field_idx];

			fbAddr addr = {};
			addr.kind = fbAddr_BitField;
			addr.base = base_addr.base;
			addr.type = result_type;
			addr.bitfield.bit_offset = cast(u32)bit_offset;
			addr.bitfield.bit_count  = cast(u32)bit_size;
			return addr;
		}

		fbAddr addr = {};
		addr.kind = fbAddr_Default;
		addr.base = base_ptr;
		addr.type = result_type;
		return addr;
	}

	case Ast_IndexExpr: {
		ast_node(ie, IndexExpr, expr);
		Type *expr_type = base_type(type_of_expr(ie->expr));

		// Dereference pointers to maps/containers
		if (is_type_pointer(expr_type)) {
			expr_type = base_type(type_deref(expr_type));
		}

		if (is_type_map(expr_type)) {
			// Map index: m[key] → fbAddr_Map
			fbAddr map_addr = fb_build_addr(b, ie->expr);
			fbValue key = fb_build_expr(b, ie->index);
			key = fb_emit_conv(b, key, expr_type->Map.key);

			fbValue map_ptr = map_addr.base;
			if (is_type_pointer(type_of_expr(ie->expr))) {
				map_ptr = fb_emit_load(b, map_ptr, t_rawptr);
				map_ptr.type = alloc_type_pointer(expr_type);
			}

			Type *result_type = type_of_expr(expr);
			fbAddr addr = {};
			addr.kind = fbAddr_Map;
			addr.base = map_ptr;
			addr.type = result_type;
			addr.map.key = key;
			addr.map.map_type = expr_type;
			addr.map.result_type = result_type;
			return addr;
		}

		fbAddr base_addr = fb_build_addr(b, ie->expr);
		fbValue index = fb_build_expr(b, ie->index);

		// Dereference pointer-to-container: ^[N]T, ^[]T, etc.
		// The address gives us a pointer to the pointer; we must load
		// through it to get the actual container base.
		bool deref = is_type_pointer(base_type(base_addr.type));
		Type *bt = base_type(base_addr.type);
		if (deref) {
			bt = base_type(type_deref(bt));
		}

		Type *elem_type = nullptr;
		i64 stride = 0;

		fbValue data_ptr = base_addr.base;

		if (bt->kind == Type_Array) {
			elem_type = bt->Array.elem;
			stride = type_size_of(elem_type);
			if (deref) {
				data_ptr = fb_emit_load(b, base_addr.base, t_rawptr);
			}
		} else if (bt->kind == Type_Slice) {
			elem_type = bt->Slice.elem;
			stride = type_size_of(elem_type);
			if (deref) {
				data_ptr = fb_emit_load(b, base_addr.base, t_rawptr);
			}
			data_ptr = fb_emit_load(b, data_ptr, t_rawptr);
		} else if (bt->kind == Type_DynamicArray) {
			elem_type = bt->DynamicArray.elem;
			stride = type_size_of(elem_type);
			if (deref) {
				data_ptr = fb_emit_load(b, base_addr.base, t_rawptr);
			}
			data_ptr = fb_emit_load(b, data_ptr, t_rawptr);
		} else if (is_type_string(bt)) {
			elem_type = t_u8;
			stride = 1;
			if (deref) {
				data_ptr = fb_emit_load(b, base_addr.base, t_rawptr);
			}
			data_ptr = fb_emit_load(b, data_ptr, t_rawptr);
		} else if (is_type_pointer(bt)) {
			elem_type = bt->Pointer.elem;
			stride = type_size_of(elem_type);
			data_ptr = fb_emit_load(b, base_addr.base, t_rawptr);
		} else if (is_type_multi_pointer(bt)) {
			elem_type = bt->MultiPointer.elem;
			stride = type_size_of(elem_type);
			data_ptr = fb_emit_load(b, base_addr.base, t_rawptr);
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

			if (se->high == nullptr) {
				// p[low:] → pointer arithmetic, result is [^]T
				fbValue offset = fb_emit_array_access(b, data_ptr, low, stride);
				Type *mp_type = type_of_expr(expr);
				fbAddr local = fb_add_local(b, mp_type, nullptr, false);
				fb_emit_store(b, local.base, offset);
				return local;
			}

			result_type = alloc_type_slice(bt->MultiPointer.elem);
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

	case Ast_CallExpr: {
		ast_node(ce, CallExpr, expr);
		TypeAndValue proc_tv = type_and_value_of_expr(ce->proc);

		if (proc_tv.mode == Addressing_Builtin) {
			Ast *proc_expr = unparen_expr(ce->proc);
			Entity *e = entity_of_node(proc_expr);
			if (e != nullptr && cast(BuiltinProcId)e->Builtin.id == BuiltinProc_swizzle) {
				TypeAndValue tv = expr->tav;
				if (is_type_array(tv.type)) {
					isize index_count = ce->args.count - 1;
					fbAddr src_addr = fb_build_addr(b, ce->args[0]);
					Type *src_type = base_type(type_of_expr(ce->args[0]));
					i64 count = src_type->Array.count;

					if (count <= 4 && index_count <= 4) {
						u8 indices[4] = {};
						u8 idx_count = 0;
						for (isize i = 0; i < index_count; i++) {
							TypeAndValue itv = type_and_value_of_expr(ce->args[i + 1]);
							indices[idx_count++] = cast(u8)big_int_to_i64(&itv.value.value_integer);
						}
						fbAddr addr = {};
						addr.kind = fbAddr_Swizzle;
						addr.base = src_addr.base;
						addr.type = tv.type;
						addr.swizzle.count = idx_count;
						addr.swizzle.indices[0] = indices[0];
						addr.swizzle.indices[1] = indices[1];
						addr.swizzle.indices[2] = indices[2];
						addr.swizzle.indices[3] = indices[3];
						return addr;
					}

					auto indices = slice_make<i32>(permanent_allocator(), index_count);
					for (isize i = 0; i < index_count; i++) {
						TypeAndValue itv = type_and_value_of_expr(ce->args[i + 1]);
						indices[i] = cast(i32)big_int_to_i64(&itv.value.value_integer);
					}
					fbAddr addr = {};
					addr.kind = fbAddr_SwizzleLarge;
					addr.base = src_addr.base;
					addr.type = tv.type;
					addr.swizzle_large.indices = indices;
					return addr;
				}
			}
		}

		// Call result needs to be addressable (e.g., for slicing).
		// Build the call, store to a temp local, return the local's addr.
		fbValue val = fb_build_expr(b, expr);
		Type *type = type_of_expr(expr);
		fbAddr temp = fb_add_local(b, type, nullptr, false);
		fb_emit_copy_value(b, temp.base, val, type);
		return temp;
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

	// Aggregate → Aggregate (FBT_VOID → FBT_VOID, different Odin types): rebrand
	if (src_ft.kind == FBT_VOID && dst_ft.kind == FBT_VOID) {
		val.type = dst_type;
		return val;
	}

	// Aggregate → Scalar: the fast backend represents aggregates as pointers
	// to stack memory. Load the destination scalar type from that pointer.
	if (src_ft.kind == FBT_VOID && dst_ft.kind != FBT_VOID) {
		return fb_emit_load(b, val, dst_type);
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
	if (cl->elems.count == 0 && bt->kind != Type_Map) {
		// Empty compound literal: zero-init is sufficient
		// (maps still need allocator setup even when empty)
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

	case Type_BitSet: {
		// BitSet compound literal: {.Elem1, .Elem2, ...}
		// BitSets are scalar integers in the fast backend (fb_data_type delegates
		// to bit_set_to_int). Each element is an enum/int value; the corresponding
		// bit (value - lower) is set in the result.
		Type *int_type = bit_set_to_int(bt);
		i64 lower = bt->BitSet.lower;

		// Try constant-folding: if all elements are compile-time constants,
		// emit a single ICONST + STORE instead of per-element OR chains.
		bool all_const = true;
		i64 const_bits = 0;
		for_array(i, cl->elems) {
			Ast *elem = cl->elems[i];
			GB_ASSERT(elem->kind != Ast_FieldValue);
			TypeAndValue tv = type_and_value_of_expr(elem);
			if (tv.mode != Addressing_Constant) {
				all_const = false;
				break;
			}
			i64 val = exact_value_to_i64(tv.value);
			const_bits |= (cast(i64)1 << (val - lower));
		}

		if (all_const) {
			fbValue bits = fb_emit_iconst(b, int_type, const_bits);
			fb_emit_store(b, v.base, bits);
		} else {
			for_array(i, cl->elems) {
				Ast *elem = cl->elems[i];
				GB_ASSERT(elem->kind != Ast_FieldValue);
				fbValue e = fb_build_expr(b, elem);
				e = fb_emit_conv(b, e, int_type);
				fbValue shift = fb_emit_arith(b, FB_SUB, e,
					fb_emit_iconst(b, int_type, lower), int_type);
				fbValue bit = fb_emit_arith(b, FB_SHL,
					fb_emit_iconst(b, int_type, 1), shift, int_type);
				fbValue old_val = fb_emit_load(b, v.base, int_type);
				fbValue new_val = fb_emit_arith(b, FB_OR, old_val, bit, int_type);
				fb_emit_store(b, v.base, new_val);
			}
		}
		break;
	}

	case Type_Slice: {
		// Slice compound literal: []T{a, b, c}
		// 1. Allocate backing array on stack
		// 2. Populate elements
		// 3. Build slice struct {data_ptr, len}
		Type *elem_type = bt->Slice.elem;
		i64 elem_count = cl->elems.count;
		i64 stride = type_size_of(elem_type);
		i64 ptr_size = b->module->target.ptr_size;

		Type *backing_type = alloc_type_array(elem_type, elem_count);
		fbAddr backing = fb_add_local(b, backing_type, nullptr, true);

		for (i64 i = 0; i < elem_count; i++) {
			Ast *elem_expr = cl->elems[i];
			if (elem_expr->kind == Ast_FieldValue) {
				elem_expr = elem_expr->FieldValue.value;
			}
			fbValue val = fb_build_expr(b, elem_expr);
			val = fb_emit_conv(b, val, elem_type);
			fbValue dst = backing.base;
			if (i > 0) dst = fb_emit_member(b, backing.base, i * stride);
			fb_emit_copy_value(b, dst, val, elem_type);
		}

		// Store data pointer at offset 0
		fb_emit_store(b, v.base, backing.base);
		// Store length at offset ptr_size
		fbValue len_ptr = fb_emit_member(b, v.base, ptr_size);
		fb_emit_store(b, len_ptr, fb_emit_iconst(b, t_int, elem_count));
		break;
	}

	case Type_SimdVector: {
		// SimdVector compound literal: #simd[N]T{e0, e1, ..., eN-1}
		// Elements are stored contiguously in memory.
		Type *elem_type = bt->SimdVector.elem;
		i64 elem_size = type_size_of(elem_type);
		i64 count = bt->SimdVector.count;

		for (i64 i = 0; i < cl->elems.count && i < count; i++) {
			Ast *elem_expr = cl->elems[i];
			if (elem_expr->kind == Ast_FieldValue) {
				elem_expr = elem_expr->FieldValue.value;
			}
			fbValue val = fb_build_expr(b, elem_expr);
			val = fb_emit_conv(b, val, elem_type);
			fbValue dst = v.base;
			if (i > 0) dst = fb_emit_member(b, v.base, i * elem_size);
			fb_emit_store(b, dst, val);
		}
		break;
	}

	case Type_Map: {
		// Map compound literal: map[K]V{k1=v1, k2=v2, ...}
		// 1. Set allocator from context
		// 2. Reserve capacity
		// 3. Insert each element
		i64 ptr_size = b->module->target.ptr_size;
		i64 elem_count = cl->elems.count;

		// Set allocator: map.allocator = context.allocator
		// Allocator is at offset 2*ptr_size in Raw_Map (after data and len)
		// context.allocator is the first field of context (offset 0), and is 16 bytes
		if (b->context_stack.count > 0) {
			fbContextData *ctx = &b->context_stack[b->context_stack.count - 1];
			fbValue ctx_val = fb_addr_load(b, ctx->ctx);
			// ctx_val is now the context pointer (rawptr/^Context).
			// For Odin CC procs, this is the passed-in pointer.
			// For non-Odin procs with auto-created context, this is a pointer to the local.
			// If the context addr type is a pointer type, ctx_val is the pointer itself.
			// If it's a struct type (local context), ctx_val is the struct or its address.
			fbValue ctx_data_ptr;
			if (is_type_pointer(ctx->ctx.type)) {
				ctx_data_ptr = ctx_val;
			} else {
				// Local context: addr.base is already a pointer to the context data
				ctx_data_ptr = ctx->ctx.base;
			}
			fbValue alloc_dst = fb_emit_member(b, v.base, 2 * ptr_size);
			i64 alloc_size = type_size_of(t_allocator);
			fbValue sz = fb_emit_iconst(b, t_int, alloc_size);
			fb_emit_memcpy(b, alloc_dst, ctx_data_ptr, sz, ptr_size);
		}

		// Reserve capacity: __dynamic_map_reserve(map_ptr, map_info, 2*count, loc)
		if (elem_count > 0) {
			fbValue cap = fb_emit_iconst(b, t_uint, 2 * elem_count);
			fb_dynamic_map_reserve(b, v.base, bt, cap, expr);
		}

		// Insert each element
		for (i64 i = 0; i < elem_count; i++) {
			Ast *elem = cl->elems[i];
			GB_ASSERT(elem->kind == Ast_FieldValue);
			Ast *key_expr = elem->FieldValue.field;
			Ast *val_expr = elem->FieldValue.value;

			fbValue key = fb_build_expr(b, key_expr);
			key = fb_emit_conv(b, key, bt->Map.key);
			fbValue value = fb_build_expr(b, val_expr);
			value = fb_emit_conv(b, value, bt->Map.value);

			// Store value to local
			Type *value_type = bt->Map.value;
			fbAddr val_local = fb_add_local(b, value_type, nullptr, false);
			fb_emit_copy_value(b, val_local.base, value, value_type);
			fbValue val_ptr = val_local.base;
			val_ptr.type = t_rawptr;

			fbValue key_ptr = {};
			fbValue hash = fb_map_key_hash(b, v.base, bt, key, &key_ptr);
			fb_dynamic_map_set(b, v.base, bt, hash, key_ptr, val_ptr, expr);
		}
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

gb_internal fbValue fb_emit_complex_arith(fbBuilder *b, TokenKind op, fbValue lhs, fbValue rhs, Type *type) {
	Type *ft = base_complex_elem_type(type);
	i64 es = type_size_of(ft);

	// Extract components: complex = {real, imag}
	fbValue a = fb_emit_load(b, lhs, ft);                            // lhs.real
	fbValue c = fb_emit_load(b, rhs, ft);                            // rhs.real
	fbValue a_imag = fb_emit_load(b, fb_emit_member(b, lhs, es), ft); // lhs.imag
	fbValue c_imag = fb_emit_load(b, fb_emit_member(b, rhs, es), ft); // rhs.imag

	fbAddr result = fb_add_local(b, type, nullptr, true);
	fbValue real, imag;

	switch (op) {
	case Token_Add:
		real = fb_emit_arith(b, FB_FADD, a, c, ft);
		imag = fb_emit_arith(b, FB_FADD, a_imag, c_imag, ft);
		break;
	case Token_Sub:
		real = fb_emit_arith(b, FB_FSUB, a, c, ft);
		imag = fb_emit_arith(b, FB_FSUB, a_imag, c_imag, ft);
		break;
	case Token_Mul: {
		// (a+bi)(c+di) = (ac-bd) + (ad+bc)i
		fbValue ac = fb_emit_arith(b, FB_FMUL, a, c, ft);
		fbValue bd = fb_emit_arith(b, FB_FMUL, a_imag, c_imag, ft);
		real = fb_emit_arith(b, FB_FSUB, ac, bd, ft);
		fbValue ad = fb_emit_arith(b, FB_FMUL, a, c_imag, ft);
		fbValue bc = fb_emit_arith(b, FB_FMUL, a_imag, c, ft);
		imag = fb_emit_arith(b, FB_FADD, ad, bc, ft);
		break;
	}
	case Token_Quo: {
		// (a+bi)/(c+di) = ((ac+bd) + (bc-ad)i) / (c²+d²)
		fbValue cc = fb_emit_arith(b, FB_FMUL, c, c, ft);
		fbValue dd = fb_emit_arith(b, FB_FMUL, c_imag, c_imag, ft);
		fbValue denom = fb_emit_arith(b, FB_FADD, cc, dd, ft);
		fbValue ac = fb_emit_arith(b, FB_FMUL, a, c, ft);
		fbValue bd = fb_emit_arith(b, FB_FMUL, a_imag, c_imag, ft);
		fbValue num_r = fb_emit_arith(b, FB_FADD, ac, bd, ft);
		real = fb_emit_arith(b, FB_FDIV, num_r, denom, ft);
		fbValue bc = fb_emit_arith(b, FB_FMUL, a_imag, c, ft);
		fbValue ad = fb_emit_arith(b, FB_FMUL, a, c_imag, ft);
		fbValue num_i = fb_emit_arith(b, FB_FSUB, bc, ad, ft);
		imag = fb_emit_arith(b, FB_FDIV, num_i, denom, ft);
		break;
	}
	default: GB_PANIC("invalid complex op"); real = imag = fb_value_nil(); break;
	}

	fb_emit_store(b, result.base, real);
	fb_emit_store(b, fb_emit_member(b, result.base, es), imag);
	result.base.type = type;
	return result.base;
}

gb_internal fbValue fb_emit_quaternion_arith(fbBuilder *b, TokenKind op, fbValue lhs, fbValue rhs, Type *type) {
	Type *ft = base_complex_elem_type(type);
	i64 es = type_size_of(ft);

	// @QuaternionLayout: {i, j, k, w} at indices {0, 1, 2, 3}
	fbValue li = fb_emit_load(b, lhs, ft);
	fbValue lj = fb_emit_load(b, fb_emit_member(b, lhs, es * 1), ft);
	fbValue lk = fb_emit_load(b, fb_emit_member(b, lhs, es * 2), ft);
	fbValue lw = fb_emit_load(b, fb_emit_member(b, lhs, es * 3), ft);

	fbValue ri = fb_emit_load(b, rhs, ft);
	fbValue rj = fb_emit_load(b, fb_emit_member(b, rhs, es * 1), ft);
	fbValue rk = fb_emit_load(b, fb_emit_member(b, rhs, es * 2), ft);
	fbValue rw = fb_emit_load(b, fb_emit_member(b, rhs, es * 3), ft);

	fbAddr result = fb_add_local(b, type, nullptr, true);
	fbValue oi, oj, ok, ow;

	switch (op) {
	case Token_Add:
		oi = fb_emit_arith(b, FB_FADD, li, ri, ft);
		oj = fb_emit_arith(b, FB_FADD, lj, rj, ft);
		ok = fb_emit_arith(b, FB_FADD, lk, rk, ft);
		ow = fb_emit_arith(b, FB_FADD, lw, rw, ft);
		break;
	case Token_Sub:
		oi = fb_emit_arith(b, FB_FSUB, li, ri, ft);
		oj = fb_emit_arith(b, FB_FSUB, lj, rj, ft);
		ok = fb_emit_arith(b, FB_FSUB, lk, rk, ft);
		ow = fb_emit_arith(b, FB_FSUB, lw, rw, ft);
		break;
	case Token_Mul: {
		// Hamilton product:
		// w = lw*rw - li*ri - lj*rj - lk*rk
		// i = lw*ri + li*rw + lj*rk - lk*rj
		// j = lw*rj - li*rk + lj*rw + lk*ri
		// k = lw*rk + li*rj - lj*ri + lk*rw
		fbValue t0, t1, t2, t3;

		t0 = fb_emit_arith(b, FB_FMUL, lw, rw, ft);
		t1 = fb_emit_arith(b, FB_FMUL, li, ri, ft);
		t0 = fb_emit_arith(b, FB_FSUB, t0, t1, ft);
		t1 = fb_emit_arith(b, FB_FMUL, lj, rj, ft);
		t0 = fb_emit_arith(b, FB_FSUB, t0, t1, ft);
		t1 = fb_emit_arith(b, FB_FMUL, lk, rk, ft);
		ow = fb_emit_arith(b, FB_FSUB, t0, t1, ft);

		t0 = fb_emit_arith(b, FB_FMUL, lw, ri, ft);
		t1 = fb_emit_arith(b, FB_FMUL, li, rw, ft);
		t0 = fb_emit_arith(b, FB_FADD, t0, t1, ft);
		t1 = fb_emit_arith(b, FB_FMUL, lj, rk, ft);
		t0 = fb_emit_arith(b, FB_FADD, t0, t1, ft);
		t1 = fb_emit_arith(b, FB_FMUL, lk, rj, ft);
		oi = fb_emit_arith(b, FB_FSUB, t0, t1, ft);

		t0 = fb_emit_arith(b, FB_FMUL, lw, rj, ft);
		t1 = fb_emit_arith(b, FB_FMUL, li, rk, ft);
		t0 = fb_emit_arith(b, FB_FSUB, t0, t1, ft);
		t1 = fb_emit_arith(b, FB_FMUL, lj, rw, ft);
		t0 = fb_emit_arith(b, FB_FADD, t0, t1, ft);
		t1 = fb_emit_arith(b, FB_FMUL, lk, ri, ft);
		oj = fb_emit_arith(b, FB_FADD, t0, t1, ft);

		t0 = fb_emit_arith(b, FB_FMUL, lw, rk, ft);
		t1 = fb_emit_arith(b, FB_FMUL, li, rj, ft);
		t0 = fb_emit_arith(b, FB_FADD, t0, t1, ft);
		t1 = fb_emit_arith(b, FB_FMUL, lj, ri, ft);
		t0 = fb_emit_arith(b, FB_FSUB, t0, t1, ft);
		t1 = fb_emit_arith(b, FB_FMUL, lk, rw, ft);
		ok = fb_emit_arith(b, FB_FADD, t0, t1, ft);
		break;
	}
	default: GB_PANIC("invalid quaternion op"); oi = oj = ok = ow = fb_value_nil(); break;
	}

	fb_emit_store(b, result.base, oi);
	fb_emit_store(b, fb_emit_member(b, result.base, es * 1), oj);
	fb_emit_store(b, fb_emit_member(b, result.base, es * 2), ok);
	fb_emit_store(b, fb_emit_member(b, result.base, es * 3), ow);
	result.base.type = type;
	return result.base;
}

gb_internal fbValue fb_build_binary_expr(fbBuilder *b, Ast *expr) {
	ast_node(be, BinaryExpr, expr);

	TypeAndValue tv = type_and_value_of_expr(expr);
	Type *type = default_type(tv.type);

	// Complex/quaternion arithmetic (aggregate types with special semantics)
	if (is_type_complex(type)) {
		if (be->op.kind == Token_Add || be->op.kind == Token_Sub ||
		    be->op.kind == Token_Mul || be->op.kind == Token_Quo) {
			fbValue left  = fb_build_expr(b, be->left);
			fbValue right = fb_build_expr(b, be->right);
			return fb_emit_complex_arith(b, be->op.kind, left, right, type);
		}
	}
	if (is_type_quaternion(type)) {
		if (be->op.kind == Token_Add || be->op.kind == Token_Sub ||
		    be->op.kind == Token_Mul) {
			fbValue left  = fb_build_expr(b, be->left);
			fbValue right = fb_build_expr(b, be->right);
			return fb_emit_quaternion_arith(b, be->op.kind, left, right, type);
		}
	}

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
			if (orig->kind == Ast_BasicDirective) {
				// Bare #caller_expression: convert the call expression to a string
				gbString expr_str = expr_to_string(call_expr, temporary_allocator());
				String s = make_string_c(expr_str);
				ExactValue sv = exact_value_string(s);
				return fb_const_value(b, t_string, sv);
			}
			// Parametrized #caller_expression(param_name):
			// Find the referenced parameter's argument at the call site.
			if (orig->kind == Ast_CallExpr && orig->CallExpr.proc->kind == Ast_BasicDirective) {
				GB_ASSERT(orig->CallExpr.args.count == 1);
				Ast *target = orig->CallExpr.args[0];
				GB_ASSERT(target->kind == Ast_Ident);
				String target_str = target->Ident.token.string;

				// Look up the parameter index in the callee's procedure type
				ast_node(ce, CallExpr, call_expr);
				Type *callee_type = type_of_expr(ce->proc);
				if (callee_type != nullptr) callee_type = base_type(callee_type);
				isize param_idx = -1;
				if (callee_type != nullptr && callee_type->kind == Type_Proc) {
					param_idx = lookup_procedure_parameter(callee_type, target_str);
				}

				// Find the corresponding argument at the call site
				Ast *target_expr = nullptr;
				if (param_idx >= 0 && ce->split_args != nullptr) {
					if (ce->split_args->positional.count > param_idx) {
						target_expr = ce->split_args->positional[param_idx];
					}
					for_array(i, ce->split_args->named) {
						Ast *arg = ce->split_args->named[i];
						ast_node(fv, FieldValue, arg);
						if (fv->field->kind == Ast_Ident && fv->field->Ident.token.string == target_str) {
							target_expr = fv->value;
							break;
						}
					}
				}

				gbString expr_str = expr_to_string(target_expr, temporary_allocator());
				String s = make_string_c(expr_str);
				ExactValue sv = exact_value_string(s);
				return fb_const_value(b, t_string, sv);
			}
			return fb_build_expr(b, orig);
		}
		// Fallthrough to zero
		fbAddr nil_val = fb_add_local(b, param_type, nullptr, true);
		nil_val.base.type = param_type;
		return nil_val.base;
	}

	case ParameterValue_Value:
		return fb_build_expr(b, pv.ast_value);

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
	bool is_odin_like = false;
	bool has_context  = false;
	TypeTuple *results = nullptr;
	i32 result_count = 0;

	if (proc_type != nullptr && proc_type->kind == Type_Proc) {
		is_odin_like = is_calling_convention_odin(proc_type->Proc.calling_convention);
		has_context  = (proc_type->Proc.calling_convention == ProcCC_Odin);
		if (proc_type->Proc.results != nullptr) {
			results = &proc_type->Proc.results->Tuple;
			result_count = cast(i32)results->variables.count;
		}
	}

	// For Odin CC: values passed via hidden output pointers.
	// Multi-return: values 0..N-2 get split temps.
	// Single-return MEMORY-class: the sole result also needs a temp.
	i32 split_count = (is_odin_like && result_count > 1) ? (result_count - 1) : 0;
	fbAddr *split_temps = nullptr;
	bool sret_single = false; // single MEMORY-class return via hidden output pointer
	fbAddr sret_temp = {};

	if (split_count > 0) {
		split_temps = gb_alloc_array(heap_allocator(), fbAddr, split_count);
		for (i32 i = 0; i < split_count; i++) {
			split_temps[i] = fb_add_local(b, results->variables[i]->type, nullptr, true);
		}
	}

	// Check if the last/sole return type is an aggregate (FBT_VOID).
	// The fast backend IR can't represent multi-register aggregate returns,
	// so any aggregate return (including small INTEGER×2 structs like Allocator)
	// must use a hidden output pointer (sret).
	if (!sret_single && result_count >= 1 && split_count == 0) {
		Type *ret_type = results->variables[result_count - 1]->type;
		fbType ret_ft = fb_data_type(ret_type);
		if (ret_ft.kind == FBT_VOID) {
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

		// Build explicit positional arguments.
		// Compile-time params (TypeName, Constant) are erased — emit nil/const
		// without evaluating the AST expression (which may be a type literal
		// like map[K]V that fb_build_expr cannot handle).
		for_array(i, ce->args) {
			Entity *e = (params != nullptr && i < param_count) ? params->variables[i] : nullptr;
			if (e != nullptr && e->kind == Entity_TypeName) {
				built_args[i].val  = fb_emit_iconst(b, t_rawptr, 0);
				built_args[i].type = e->type;
				continue;
			}
			if (e != nullptr && e->kind == Entity_Constant) {
				built_args[i].val  = fb_const_value(b, e->type, e->Constant.value);
				built_args[i].type = e->type;
				continue;
			}
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
			if (!is_odin_like && abi.num_classes >= 1 && abi.classes[0] == FB_ABI_SSE && aux_idx < 32) {
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
	if (has_context) {
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
		if (is_odin_like) {
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
	u8 cc_flag = is_odin_like ? FBCC_ODIN : FBCC_C;
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
			if (idx == nullptr) {
				// Lazily add runtime/library procs not discovered during initial scan
				fbProc *p = fb_proc_create(b->module, e);
				u32 proc_idx = cast(u32)b->module->procs.count;
				array_add(&b->module->procs, p);
				map_set(&fb_entity_proc_map, e, proc_idx);
				idx = map_get(&fb_entity_proc_map, e);
			}
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

		// Determine if the inner expression returns a tuple (multi-return)
		// or a single value. For single-return or_return (e.g. `foo() or_return`
		// where foo returns Allocator_Error), the single value IS the rhs
		// (error) and there is no lhs (value).
		fbValue value = {};
		fbValue rhs = {};
		Type *inner_type = type_of_expr(ore->expr);
		if (inner_type != nullptr && inner_type->kind == Type_Tuple) {
			// Multi-return: unpack into value(s) + rhs
			fbValue vals[2];
			fb_unpack_multi_return(b, last_val, vals, 2);
			value = vals[0];
			rhs   = vals[1];
		} else {
			// Single return: the value IS the error/ok
			rhs = last_val;
			// value stays empty — or_return yields nothing (Addressing_NoValue)
		}

		u32 ok_block     = fb_new_block(b);
		u32 return_block = fb_new_block(b);

		// Check if rhs indicates success:
		// - boolean types: true = has value
		// - other types (enums etc with nil): nil = has value (no error)
		fbValue has_value;
		if (is_type_boolean(rhs.type)) {
			has_value = fb_emit_conv(b, rhs, t_bool);
		} else {
			// Compare against nil (zero): rhs == 0 means no error = has value
			fbValue zero = fb_emit_iconst(b, rhs.type, 0);
			has_value = fb_emit_cmp(b, FB_CMP_EQ, rhs, zero);
		}
		fb_emit_branch(b, has_value, ok_block, return_block);

		// Return block: rhs indicates error, return the error value.
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
		// Convert rhs to the caller's last return type before returning
		{
			Type *caller_pt = base_type(b->type);
			Type *caller_results = caller_pt->Proc.results;
			if (caller_results != nullptr && caller_results->kind == Type_Tuple) {
				Type *end_type = caller_results->Tuple.variables[caller_results->Tuple.variables.count - 1]->type;
				rhs = fb_emit_conv(b, rhs, end_type);
			}
		}
		fb_emit_ret(b, rhs);

		// Ok block: return the value
		fb_set_block(b, ok_block);
		if (type != nullptr && value.id != 0) {
			return fb_emit_conv(b, value, type);
		}
		// Single-return or_return: no value to yield
		return value;
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
	bool is_odin_like = is_calling_convention_odin(proc_type->calling_convention);

	TypeTuple *res_tuple = (proc_type->results != nullptr)
		? &proc_type->results->Tuple : nullptr;
	i32 res_count = res_tuple ? cast(i32)res_tuple->variables.count : 0;

	if (results.count == 0) {
		// Bare `return` — copy named results to their output locations.
		if (proc_type->has_named_results && res_count > 0) {
			if (is_odin_like && res_count > 1 && b->proc->split_returns_index >= 0) {
				// Multi-return with split returns: copy first N-1 named
				// results to split return output pointers, return last
				// in register.
				for (i32 i = 0; i < res_count - 1; i++) {
					Entity *re = res_tuple->variables[i];
					fbAddr *local = map_get(&b->variable_map, re);
					if (local == nullptr) continue;
					fbValue val = fb_addr_load(b, *local);
					Type *ret_type = re->type;
					fbType ret_ft = fb_data_type(ret_type);
					if (ret_ft.kind != FBT_VOID) {
						val = fb_emit_conv(b, val, ret_type);
					}
					fbValue out_ptr = fb_load_split_return_ptr(b, i);
					fb_emit_copy_value(b, out_ptr, val, ret_type);
				}
				Entity *last_re = res_tuple->variables[res_count - 1];
				fbAddr *last_local = map_get(&b->variable_map, last_re);
				fbValue last_val = {};
				if (last_local != nullptr) {
					last_val = fb_addr_load(b, *last_local);
					last_val = fb_emit_conv(b, last_val, last_re->type);
				} else {
					last_val = fb_emit_iconst(b, last_re->type, 0);
				}
				fb_emit_defer_stmts(b, fbDeferExit_Return, 0);
				fb_emit_ret(b, last_val);
				return;
			} else if (b->proc->sret_slot_idx >= 0 && res_count == 1) {
				// Single MEMORY-class return with sret.
				Entity *re = res_tuple->variables[0];
				fbAddr *local = map_get(&b->variable_map, re);
				if (local != nullptr) {
					fbValue sret_ptr = fb_emit_alloca_from_slot(b, cast(u32)b->proc->sret_slot_idx);
					sret_ptr = fb_emit_load(b, sret_ptr, alloc_type_pointer(re->type));
					i64 sz = type_size_of(re->type);
					i64 al = type_align_of(re->type);
					fbValue sz_val = fb_emit_iconst(b, t_uintptr, sz);
					fb_emit_memcpy(b, sret_ptr, local->base, sz_val, al);
				}
			} else if (res_count == 1) {
				// Single scalar return with named result.
				Entity *re = res_tuple->variables[0];
				fbAddr *local = map_get(&b->variable_map, re);
				if (local != nullptr) {
					fbValue val = fb_addr_load(b, *local);
					val = fb_emit_conv(b, val, re->type);
					fb_emit_defer_stmts(b, fbDeferExit_Return, 0);
					fb_emit_ret(b, val);
					return;
				}
			}
		}
		fb_emit_defer_stmts(b, fbDeferExit_Return, 0);
		fb_emit_ret_void(b);
		return;
	}

	if (results.count == 1 && !(is_odin_like && res_count > 1)) {
		// Single return value (the common case)
		fbValue val = fb_build_expr(b, results[0]);
		Type *ret_type = nullptr;
		if (is_odin_like && res_count > 0) {
			ret_type = res_tuple->variables[res_count - 1]->type;
		} else if (res_count > 0) {
			ret_type = res_tuple->variables[0]->type;
		}
		if (ret_type != nullptr) {
			val = fb_emit_conv(b, val, ret_type);
		}
		fb_emit_defer_stmts(b, fbDeferExit_Return, 0);

		// If the proc uses sret (single MEMORY-class return), copy the result
		// to the caller's output buffer and return void.
		if (b->proc->sret_slot_idx >= 0) {
			fbValue sret_ptr = fb_emit_alloca_from_slot(b, cast(u32)b->proc->sret_slot_idx);
			sret_ptr = fb_emit_load(b, sret_ptr, alloc_type_pointer(ret_type));
			i64 sz = type_size_of(ret_type);
			i64 al = type_align_of(ret_type);
			fbValue sz_val = fb_emit_iconst(b, t_uintptr, sz);
			fb_emit_memcpy(b, sret_ptr, val, sz_val, al);
			fb_emit_ret_void(b);
		} else {
			fb_emit_ret(b, val);
		}
		return;
	}

	// Multi-return (Odin CC): store first N-1 values through hidden output
	// pointer params, return the last value in a register.
	GB_ASSERT(is_odin_like && res_count > 1);
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
					fb_addr_store(b, addr, val);
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
			fb_addr_store(b, addr, val);
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

// Map range: for key, value in map_expr
gb_internal void fb_build_range_map(fbBuilder *b, AstRangeStmt *rs, Scope *scope) {
	fb_scope_open(b, scope);

	Ast *expr = unparen_expr(rs->expr);
	Type *expr_type = type_of_expr(expr);
	Type *map_type = base_type(type_deref(expr_type));
	GB_ASSERT(map_type->kind == Type_Map);

	Type *key_type = map_type->Map.key;
	Type *val_type = map_type->Map.value;

	Ast *val0 = rs->vals.count > 0 ? fb_strip_and_prefix(rs->vals[0]) : nullptr;
	Ast *val1 = rs->vals.count > 1 ? fb_strip_and_prefix(rs->vals[1]) : nullptr;

	// Load map value
	fbAddr map_addr = fb_build_addr(b, expr);
	fbValue map_ptr = map_addr.base;
	if (is_type_pointer(expr_type)) {
		map_ptr = fb_emit_load(b, map_ptr, t_rawptr);
		map_ptr.type = alloc_type_pointer(map_type);
	}

	// Load map.data field and compute capacity
	fbValue map_data = fb_emit_load(b, map_ptr, t_uintptr);
	fbValue capacity = fb_map_cap(b, map_data);
	fbValue ks = fb_map_data_uintptr(b, map_data);

	// Compute vs = cell_index(key_type, ks, capacity) → start of value cells
	fbValue vs = fb_map_cell_index(b, key_type, ks, capacity);
	vs = fb_emit_conv(b, vs, t_rawptr);

	// Compute hs = cell_index(val_type, vs, capacity) → start of hash cells
	fbValue hs = fb_map_cell_index(b, val_type, vs, capacity);
	hs = fb_emit_conv(b, hs, t_rawptr);

	// Index: start at -1
	fbAddr index_addr = fb_add_local(b, t_int, nullptr, false);
	fb_addr_store(b, index_addr, fb_emit_iconst(b, t_int, -1));

	u32 loop_block = fb_new_block(b);
	u32 hash_check = fb_new_block(b);
	u32 body_block = fb_new_block(b);
	u32 done_block = fb_new_block(b);

	// Register label targets
	if (rs->label != nullptr) {
		for_array(i, b->branch_regions) {
			if (b->branch_regions[i].cond == rs->label) {
				b->branch_regions[i].false_block = done_block;
				b->branch_regions[i].true_block  = loop_block;
				break;
			}
		}
	}

	// Set up break/continue targets
	fbTargetList tl = {};
	tl.break_block    = done_block;
	tl.continue_block = loop_block;
	tl.prev           = b->target_list;
	b->target_list    = &tl;

	fb_emit_jump(b, loop_block);
	fb_set_block(b, loop_block);

	// Increment index
	fbValue idx = fb_addr_load(b, index_addr);
	fbValue one = fb_emit_iconst(b, t_int, 1);
	fbValue incr = fb_emit_arith(b, FB_ADD, idx, one, t_int);
	fb_addr_store(b, index_addr, incr);

	// Check: index < capacity
	fbValue cap_int = fb_emit_conv(b, capacity, t_int);
	fbValue in_range = fb_emit_cmp(b, FB_CMP_SLT, incr, cap_int);
	fb_emit_branch(b, in_range, hash_check, done_block);

	// Hash check: load hash at index, check validity
	fb_set_block(b, hash_check);
	// hashes are uintptr, densely packed (no cell padding for uintptr)
	fbValue hash_ptr = fb_emit_array_access(b, hs, incr, build_context.ptr_size);
	fbValue hash = fb_emit_load(b, hash_ptr, t_uintptr);
	fbValue valid = fb_map_hash_is_valid(b, hash);
	fb_emit_branch(b, valid, body_block, loop_block);

	// Body: load key and value, bind variables
	fb_set_block(b, body_block);
	fbValue key_ptr = fb_map_cell_index(b, key_type, ks, incr);
	fbValue val_ptr = fb_map_cell_index(b, val_type, vs, incr);

	// val0 = key, val1 = value (in Odin: for key, value in m)
	if (val0 != nullptr && !is_blank_ident(val0)) {
		Type *v0t = type_of_expr(val0);
		Entity *e0 = entity_of_node(val0);
		fbAddr k_addr = fb_add_local(b, v0t, e0, false);
		fbType kft = fb_data_type(key_type);
		if (kft.kind != FBT_VOID) {
			fbValue k = fb_emit_load(b, key_ptr, key_type);
			k = fb_emit_conv(b, k, v0t);
			fb_emit_store(b, k_addr.base, k);
		} else {
			i64 ksz = type_size_of(key_type);
			if (ksz > 0) {
				fbValue sz = fb_emit_iconst(b, t_int, ksz);
				fb_emit_memcpy(b, k_addr.base, key_ptr, sz, type_align_of(key_type));
			}
		}
	}

	if (val1 != nullptr && !is_blank_ident(val1)) {
		Type *v1t = type_of_expr(val1);
		Entity *e1 = entity_of_node(val1);
		fbAddr v_addr = fb_add_local(b, v1t, e1, false);
		fbType vft = fb_data_type(val_type);
		if (vft.kind != FBT_VOID) {
			fbValue v = fb_emit_load(b, val_ptr, val_type);
			v = fb_emit_conv(b, v, v1t);
			fb_emit_store(b, v_addr.base, v);
		} else {
			i64 vsz = type_size_of(val_type);
			if (vsz > 0) {
				fbValue sz = fb_emit_iconst(b, t_int, vsz);
				fb_emit_memcpy(b, v_addr.base, val_ptr, sz, type_align_of(val_type));
			}
		}
	}

	// Execute body
	fb_build_stmt(b, rs->body);

	b->target_list = tl.prev;

	if (!fb_block_is_terminated(b)) {
		fb_emit_jump(b, loop_block);
	}

	fb_set_block(b, done_block);
	fb_scope_close(b, fbDeferExit_Default, 0);
}

// String range: for rune, idx in string
gb_internal void fb_build_range_string(fbBuilder *b, AstRangeStmt *rs, Scope *scope) {
	// For byte strings, iterate byte-by-byte
	fb_scope_open(b, scope);

	Ast *expr = unparen_expr(rs->expr);
	fbAddr base_addr = fb_build_addr(b, expr);
	fbValue data_ptr = fb_emit_load(b, base_addr.base, t_rawptr);
	fbValue length = fb_load_field(b, base_addr.base, build_context.ptr_size, t_int);

	Ast *val0 = rs->vals.count > 0 ? fb_strip_and_prefix(rs->vals[0]) : nullptr;
	Ast *val1 = rs->vals.count > 1 ? fb_strip_and_prefix(rs->vals[1]) : nullptr;

	fbAddr index_addr = fb_add_local(b, t_int, nullptr, false);
	fb_addr_store(b, index_addr, fb_emit_iconst(b, t_int, -1));

	u32 loop_block = fb_new_block(b);
	u32 body_block = fb_new_block(b);
	u32 done_block = fb_new_block(b);

	if (rs->label != nullptr) {
		for_array(i, b->branch_regions) {
			if (b->branch_regions[i].cond == rs->label) {
				b->branch_regions[i].false_block = done_block;
				b->branch_regions[i].true_block  = loop_block;
				break;
			}
		}
	}

	fbTargetList tl = {};
	tl.break_block    = done_block;
	tl.continue_block = loop_block;
	tl.prev           = b->target_list;
	b->target_list    = &tl;

	fb_emit_jump(b, loop_block);
	fb_set_block(b, loop_block);

	fbValue idx = fb_addr_load(b, index_addr);
	fbValue one = fb_emit_iconst(b, t_int, 1);
	fbValue incr = fb_emit_arith(b, FB_ADD, idx, one, t_int);
	fb_addr_store(b, index_addr, incr);

	fbValue in_range = fb_emit_cmp(b, FB_CMP_SLT, incr, length);
	fb_emit_branch(b, in_range, body_block, done_block);

	fb_set_block(b, body_block);

	// val0 = byte value, val1 = index
	if (val0 != nullptr && !is_blank_ident(val0)) {
		Entity *e0 = entity_of_node(val0);
		Type *v0t = type_of_expr(val0);
		fbAddr ch_addr = fb_add_local(b, v0t, e0, false);
		fbValue char_ptr = fb_emit_array_access(b, data_ptr, incr, 1);
		fbValue ch = fb_emit_load(b, char_ptr, t_u8);
		ch = fb_emit_conv(b, ch, v0t);
		fb_emit_store(b, ch_addr.base, ch);
	}
	if (val1 != nullptr && !is_blank_ident(val1)) {
		Entity *e1 = entity_of_node(val1);
		Type *v1t = type_of_expr(val1);
		fbAddr idx_var = fb_add_local(b, v1t, e1, false);
		fbValue idx_conv = fb_emit_conv(b, incr, v1t);
		fb_emit_store(b, idx_var.base, idx_conv);
	}

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
	case Type_Map:
		fb_build_range_map(b, rs, rs->scope);
		return;
	case Type_Basic:
		if (is_type_string(et)) {
			fb_build_range_string(b, rs, rs->scope);
			return;
		}
		break;
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
			ctx_addr.type = alloc_type_pointer(t_context); // rawptr→^Context for field access

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

	// Force-compute type sizes for map-related types.
	// Some runtime types may not have cached_size set yet, and trying to
	// compute them during code generation can crash if the Type object is
	// in read-only memory.
	if (t_raw_map) type_size_of(t_raw_map);
	if (t_map_info) type_size_of(t_map_info);
	if (t_map_cell_info) type_size_of(t_map_cell_info);
	if (t_allocator) type_size_of(t_allocator);
	type_size_of(t_rawptr);
	type_size_of(t_uintptr);

	// Pre-register runtime procs needed by the fast backend that may have
	// min_dep_count == 0 (not referenced by user code, only by backend-generated IR).
	// These must be added before the build pass so their types are ready.
	{
		String runtime_procs[] = {
			str_lit("__dynamic_map_get"),
			str_lit("__dynamic_map_set"),
			str_lit("__dynamic_map_reserve"),
			str_lit("map_alloc_dynamic"),
			str_lit("map_free_dynamic"),
			str_lit("map_kvh_data_dynamic"),
			str_lit("map_cell_index_dynamic"),
			str_lit("map_insert_hash_dynamic"),
			str_lit("map_reserve_dynamic"),
			str_lit("default_hasher_string"),
			str_lit("default_hasher_cstring"),
			str_lit("default_hasher"),
			str_lit("panic"),
		};
		Scope *rt_scope = info->runtime_package->scope;
		for (isize i = 0; i < gb_count_of(runtime_procs); i++) {
			Entity *e = scope_lookup_current(rt_scope, runtime_procs[i]);
			if (e == nullptr || e->kind != Entity_Procedure) continue;
			if (map_get(&fb_entity_proc_map, e) != nullptr) continue;

			fbProc *p = fb_proc_create(m, e);
			u32 proc_idx = cast(u32)m->procs.count;
			array_add(&m->procs, p);
			map_set(&fb_entity_proc_map, e, proc_idx);
		}
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

	// Generate Runtime Type Info (RTTI) tables.
	fb_generate_type_info(m);

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
		fb_recovery_proc_name = (const char *)p->name.text;
		if (sigsetjmp(fb_recovery_buf, 1) == 0) {
			fb_procedure_generate(&b);
			fb_verify_proc(p);
			fb_recovery_active = false;
		} else {
			// Recovery: assertion fired during generation.
			// Reset the proc to an empty stub.
			stub_count++;
			gb_printf_err("  STUB: %.*s (inst_count=%d)\n", LIT(p->name), p->inst_count);
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

				// String/cstring globals: fb_serialize_const_value returns nullptr for
				// ExactValue_String. Serialize manually with a data relocation
				// for the string data pointer.
				if (entry.init_data == nullptr && tav.value.kind == ExactValue_String) {
					String str = tav.value.value_string;
					i64 ptr_size = m->target.ptr_size;
					u32 gidx = cast(u32)m->global_entries.count;

					entry.init_data = gb_alloc_array(heap_allocator(), u8, size);
					gb_zero_size(entry.init_data, size);

					if (is_type_cstring(e->type)) {
						// cstring: just a pointer (8 bytes)
						if (str.len > 0) {
							u32 rodata_sym = fb_module_intern_string_data(m, str);
							fbDataReloc dr = {};
							dr.global_idx   = gidx;
							dr.local_offset = 0;
							dr.target_sym   = rodata_sym;
							dr.addend       = 0;
							array_add(&m->data_relocs, dr);
						}
					} else {
						// Odin string: {data: rawptr, len: int}
						// Write len at offset ptr_size
						i64 slen = str.len;
						gb_memmove(entry.init_data + ptr_size, &slen, ptr_size);

						// Data pointer at offset 0 needs a relocation to rodata
						if (str.len > 0) {
							u32 rodata_sym = fb_module_intern_string_data(m, str);
							fbDataReloc dr = {};
							dr.global_idx   = gidx;
							dr.local_offset = 0;
							dr.target_sym   = rodata_sym;
							dr.addend       = 0;
							array_add(&m->data_relocs, dr);
						}
					}
				}
			}
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
