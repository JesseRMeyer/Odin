// Fast Backend — AST walker: translates Odin AST into fast backend IR
//
// Phase 6a: replaces synthetic test IR with real AST-driven code generation.
// Mirrors the Tilde backend's cg_build_stmt / cg_build_expr pattern.

// ───────────────────────────────────────────────────────────────────────
// Parameter setup: classify params via ABI, create stack slots, record param_locs
// ───────────────────────────────────────────────────────────────────────

gb_internal void fb_setup_params(fbProc *p) {
	Type *pt = base_type(p->odin_type);
	GB_ASSERT(pt != nullptr && pt->kind == Type_Proc);

	TypeProc *proc_type = &pt->Proc;
	if (proc_type->params == nullptr && proc_type->calling_convention != ProcCC_Odin) {
		return;
	}

	i32 param_count = proc_type->param_count;
	bool has_context = (proc_type->calling_convention == ProcCC_Odin);

	// Count how many GP register slots we need
	u32 gp_idx = 0;
	u32 max_gp_params = param_count + (has_context ? 1 : 0);
	if (max_gp_params == 0) return;

	// Temporary: allocate for the hard upper bound on GP register params
	u32 *locs = gb_alloc_array(heap_allocator(), u32, FB_X64_SYSV_MAX_GP_ARGS);

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
			// MEMORY class: passed on stack by caller, handled in Phase 6+
			continue;
		}

		if (abi.classes[0] == FB_ABI_SSE) {
			// SSE params: Phase 8
			continue;
		}

		// INTEGER class: each eightbyte consumes one GP register.
		// Param slots are always register-width (8 bytes, 8-aligned).
		// The SysV ABI says upper bits of narrow params are undefined,
		// so we store the full register and let the IR type system govern load width.
		for (u8 ci = 0; ci < abi.num_classes; ci++) {
			if (abi.classes[ci] != FB_ABI_INTEGER) continue;
			if (gp_idx >= FB_X64_SYSV_MAX_GP_ARGS) break; // overflow to stack

			u32 slot = fb_slot_create(p, 8, 8, e, param_type);
			locs[gp_idx++] = slot;
		}
	}

	// Odin CC: append context pointer as the last GP parameter
	if (has_context && gp_idx < FB_X64_SYSV_MAX_GP_ARGS) {
		u32 slot = fb_slot_create(p, 8, 8, nullptr, nullptr);
		locs[gp_idx++] = slot;
	}

	if (gp_idx > 0) {
		p->param_locs  = locs;
		p->param_count = gp_idx;
	} else {
		gb_free(heap_allocator(), locs);
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

// ───────────────────────────────────────────────────────────────────────
// Step 2: Builder instruction helpers
// ───────────────────────────────────────────────────────────────────────

gb_internal fbValue fb_emit(fbBuilder *b, fbOp op, fbType type, u32 a, u32 bb, u32 c, i64 imm) {
	u32 r = fb_inst_emit(b->proc, op, type, a, bb, c, 0, imm);
	fbValue val = {};
	val.id = r;
	// Determine Odin type from the fb type for common cases
	val.type = nullptr;
	return val;
}

gb_internal fbValue fb_emit_typed(fbBuilder *b, fbOp op, Type *odin_type, u32 a, u32 bb, u32 c, i64 imm) {
	fbType ft = fb_data_type(odin_type);
	u32 r = fb_inst_emit(b->proc, op, ft, a, bb, c, 0, imm);
	fbValue val = {};
	val.id = r;
	val.type = odin_type;
	return val;
}

gb_internal fbValue fb_emit_iconst(fbBuilder *b, Type *type, i64 val) {
	fbType ft = fb_data_type(type);
	if (ft.kind == FBT_VOID) ft = FB_I64;
	u32 r = fb_inst_emit(b->proc, FB_ICONST, ft, FB_NOREG, FB_NOREG, FB_NOREG, 0, val);
	fbValue v = {};
	v.id = r;
	v.type = type;
	return v;
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
	fbValue v = {};
	v.id = r;
	v.type = type;
	return v;
}

gb_internal fbValue fb_emit_load(fbBuilder *b, fbValue ptr, Type *elem_type) {
	fbType ft = fb_data_type(elem_type);
	if (ft.kind == FBT_VOID) ft = FB_I64; // aggregate: load as i64
	u32 r = fb_inst_emit(b->proc, FB_LOAD, ft, ptr.id, FB_NOREG, FB_NOREG, 0, 0);
	fbValue v = {};
	v.id = r;
	v.type = elem_type;
	return v;
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
	fbValue v = {};
	v.id = r;
	v.type = nullptr; // pointer type
	return v;
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
	fbValue v = {};
	v.id = r;
	v.type = type;
	return v;
}

gb_internal fbValue fb_emit_cmp(fbBuilder *b, fbOp cmp_op, fbValue lhs, fbValue rhs) {
	u32 r = fb_inst_emit(b->proc, cmp_op, FB_I1, lhs.id, rhs.id, FB_NOREG, 0, 0);
	fbValue v = {};
	v.id = r;
	v.type = t_bool;
	return v;
}

gb_internal fbValue fb_emit_select(fbBuilder *b, fbValue cond, fbValue t, fbValue f, Type *type) {
	fbType ft = fb_data_type(type);
	if (ft.kind == FBT_VOID) ft = FB_I64;
	u32 r = fb_inst_emit(b->proc, FB_SELECT, ft, cond.id, t.id, f.id, 0, 0);
	fbValue v = {};
	v.id = r;
	v.type = type;
	return v;
}

gb_internal void fb_emit_memzero(fbBuilder *b, fbValue ptr, i64 size, i64 align) {
	fb_inst_emit(b->proc, FB_MEMZERO, FB_VOID, ptr.id, cast(u32)align, FB_NOREG, 0, size);
}

gb_internal fbValue fb_emit_symaddr(fbBuilder *b, u32 proc_idx) {
	u32 r = fb_inst_emit(b->proc, FB_SYMADDR, FB_PTR, FB_NOREG, FB_NOREG, FB_NOREG, 0, cast(i64)proc_idx);
	fbValue v = {};
	v.id = r;
	v.type = nullptr;
	return v;
}

gb_internal fbValue fb_emit_member(fbBuilder *b, fbValue base, i64 byte_offset) {
	u32 r = fb_inst_emit(b->proc, FB_MEMBER, FB_PTR, base.id, FB_NOREG, FB_NOREG, 0, byte_offset);
	fbValue v = {};
	v.id = r;
	v.type = nullptr;
	return v;
}

gb_internal fbValue fb_emit_array_access(fbBuilder *b, fbValue base, fbValue index, i64 stride) {
	u32 r = fb_inst_emit(b->proc, FB_ARRAY, FB_PTR, base.id, index.id, FB_NOREG, 0, stride);
	fbValue v = {};
	v.id = r;
	v.type = nullptr;
	return v;
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

// Determine if an Odin type is signed integer
gb_internal bool fb_type_is_signed(Type *t) {
	t = core_type(t);
	if (t->kind == Type_Basic) {
		return (t->Basic.flags & BasicFlag_Unsigned) == 0;
	}
	if (t->kind == Type_Enum) {
		return fb_type_is_signed(t->Enum.base_type);
	}
	return true; // default to signed
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

	case ExactValue_String:
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

		// Walk the selection path
		Type *current_type = base_addr.type;
		for_array(i, sel.index) {
			i32 field_idx = sel.index[i];
			Type *bt = base_type(current_type);
			if (bt->kind == Type_Struct) {
				i64 offset = bt->Struct.offsets[field_idx];
				if (offset != 0) {
					base_ptr = fb_emit_member(b, base_ptr, offset);
				}
				current_type = bt->Struct.fields[field_idx]->type;
			} else if (is_type_pointer(bt)) {
				base_ptr = fb_emit_load(b, base_ptr, current_type);
				current_type = type_deref(current_type);
				// Retry this index on the dereferenced type
				bt = base_type(current_type);
				if (bt->kind == Type_Struct) {
					i64 offset = bt->Struct.offsets[field_idx];
					if (offset != 0) {
						base_ptr = fb_emit_member(b, base_ptr, offset);
					}
					current_type = bt->Struct.fields[field_idx]->type;
				}
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
			GB_ASSERT_MSG(b->context_stack.count > 0,
				"fb_build_addr Ast_Implicit: no context on stack");
			return b->context_stack[b->context_stack.count - 1].ctx;
		}
		break;
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

	fbType src_ft = fb_data_type(src_type);
	fbType dst_ft = fb_data_type(dst_type);

	if (fb_type_eq(src_ft, dst_ft)) {
		// Same machine type, just rebrand
		val.type = dst_type;
		return val;
	}

	i32 src_size = fb_type_size(src_ft);
	i32 dst_size = fb_type_size(dst_ft);

	// Integer → Integer conversions
	if (fb_type_is_integer(src_ft) && fb_type_is_integer(dst_ft)) {
		if (dst_size > src_size) {
			// Extend
			fbOp op = fb_type_is_signed(src_type) ? FB_SEXT : FB_ZEXT;
			u32 r = fb_inst_emit(b->proc, op, dst_ft, val.id, FB_NOREG, FB_NOREG, 0, cast(i64)fb_type_pack(src_ft));
			fbValue v = {};
			v.id = r;
			v.type = dst_type;
			return v;
		} else if (dst_size < src_size) {
			// Truncate
			u32 r = fb_inst_emit(b->proc, FB_TRUNC, dst_ft, val.id, FB_NOREG, FB_NOREG, 0, cast(i64)fb_type_pack(src_ft));
			fbValue v = {};
			v.id = r;
			v.type = dst_type;
			return v;
		}
		// Same size, just rebrand
		val.type = dst_type;
		return val;
	}

	// Bool → Integer
	if (src_ft.kind == FBT_I1 && fb_type_is_integer(dst_ft)) {
		u32 r = fb_inst_emit(b->proc, FB_ZEXT, dst_ft, val.id, FB_NOREG, FB_NOREG, 0, 0);
		fbValue v = {};
		v.id = r;
		v.type = dst_type;
		return v;
	}

	// Integer → Bool
	if (fb_type_is_integer(src_ft) && dst_ft.kind == FBT_I1) {
		fbValue zero = fb_emit_iconst(b, src_type, 0);
		return fb_emit_cmp(b, FB_CMP_NE, val, zero);
	}

	// Pointer → Pointer (no-op at IR level)
	if (src_ft.kind == FBT_PTR && dst_ft.kind == FBT_PTR) {
		val.type = dst_type;
		return val;
	}

	// Pointer → Integer
	if (src_ft.kind == FBT_PTR && fb_type_is_integer(dst_ft)) {
		u32 r = fb_inst_emit(b->proc, FB_PTR2INT, dst_ft, val.id, FB_NOREG, FB_NOREG, 0, 0);
		fbValue v = {};
		v.id = r;
		v.type = dst_type;
		return v;
	}

	// Integer → Pointer
	if (fb_type_is_integer(src_ft) && dst_ft.kind == FBT_PTR) {
		u32 r = fb_inst_emit(b->proc, FB_INT2PTR, FB_PTR, val.id, FB_NOREG, FB_NOREG, 0, 0);
		fbValue v = {};
		v.id = r;
		v.type = dst_type;
		return v;
	}

	// Float → Float conversions
	if (fb_type_is_float(src_ft) && fb_type_is_float(dst_ft)) {
		fbOp op = (dst_size > src_size) ? FB_FPEXT : FB_FPTRUNC;
		u32 r = fb_inst_emit(b->proc, op, dst_ft, val.id, FB_NOREG, FB_NOREG, 0, cast(i64)fb_type_pack(src_ft));
		fbValue v = {};
		v.id = r;
		v.type = dst_type;
		return v;
	}

	// Int → Float conversions
	if (fb_type_is_integer(src_ft) && fb_type_is_float(dst_ft)) {
		fbOp op = fb_type_is_signed(src_type) ? FB_SI2FP : FB_UI2FP;
		u32 r = fb_inst_emit(b->proc, op, dst_ft, val.id, FB_NOREG, FB_NOREG, 0, cast(i64)fb_type_pack(src_ft));
		fbValue v = {};
		v.id = r;
		v.type = dst_type;
		return v;
	}

	// Float → Int conversions
	if (fb_type_is_float(src_ft) && fb_type_is_integer(dst_ft)) {
		fbOp op = fb_type_is_signed(dst_type) ? FB_FP2SI : FB_FP2UI;
		u32 r = fb_inst_emit(b->proc, op, dst_ft, val.id, FB_NOREG, FB_NOREG, 0, cast(i64)fb_type_pack(src_ft));
		fbValue v = {};
		v.id = r;
		v.type = dst_type;
		return v;
	}

	// Bool → Float: zero-extend to i32 first, then UI2FP
	if (src_ft.kind == FBT_I1 && fb_type_is_float(dst_ft)) {
		u32 ext = fb_inst_emit(b->proc, FB_ZEXT, FB_I32, val.id, FB_NOREG, FB_NOREG, 0, 0);
		u32 r = fb_inst_emit(b->proc, FB_UI2FP, dst_ft, ext, FB_NOREG, FB_NOREG, 0, cast(i64)fb_type_pack(FB_I32));
		fbValue v = {};
		v.id = r;
		v.type = dst_type;
		return v;
	}

	// Float → Bool: compare != 0.0
	if (fb_type_is_float(src_ft) && dst_ft.kind == FBT_I1) {
		fbValue zero = fb_emit_fconst(b, src_type, 0.0);
		return fb_emit_cmp(b, FB_CMP_FNE, val, zero);
	}

	// Same-size bitcast
	if (src_size == dst_size && src_size > 0) {
		u32 r = fb_inst_emit(b->proc, FB_BITCAST, dst_ft, val.id, FB_NOREG, FB_NOREG, 0, 0);
		fbValue v = {};
		v.id = r;
		v.type = dst_type;
		return v;
	}

	GB_PANIC("fb_emit_conv: unhandled conversion from %d to %d", src_ft.kind, dst_ft.kind);
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

		fbOp op;
		switch (be->op.kind) {
		case Token_Add: op = FB_ADD; break;
		case Token_Sub: op = FB_SUB; break;
		case Token_Mul: op = FB_MUL; break;
		case Token_Quo:
			op = fb_type_is_signed(type) ? FB_SDIV : FB_UDIV;
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
			fbValue notb = {};
			notb.id = not_r;
			notb.type = type;
			return fb_emit_arith(b, FB_AND, left, notb, type);
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

		fbOp op;
		bool is_signed = fb_type_is_signed(left.type ? left.type : type);
		switch (be->op.kind) {
		case Token_CmpEq: op = FB_CMP_EQ; break;
		case Token_NotEq: op = FB_CMP_NE; break;
		case Token_Lt:    op = is_signed ? FB_CMP_SLT : FB_CMP_ULT; break;
		case Token_LtEq:  op = is_signed ? FB_CMP_SLE : FB_CMP_ULE; break;
		case Token_Gt:    op = is_signed ? FB_CMP_SGT : FB_CMP_UGT; break;
		case Token_GtEq:  op = is_signed ? FB_CMP_SGE : FB_CMP_UGE; break;
		default: GB_PANIC("unreachable"); op = FB_CMP_EQ; break;
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
		u32 r = fb_inst_emit(b->proc, FB_NEG, ft, val.id, FB_NOREG, FB_NOREG, 0, 0);
		fbValue v = {};
		v.id = r;
		v.type = type;
		return v;
	}
	case Token_Xor: {
		// Bitwise complement
		fbValue val = fb_build_expr(b, ue->expr);
		fbType ft = fb_data_type(type);
		if (ft.kind == FBT_VOID) ft = FB_I64;
		u32 r = fb_inst_emit(b->proc, FB_NOT, ft, val.id, FB_NOREG, FB_NOREG, 0, 0);
		fbValue v = {};
		v.id = r;
		v.type = type;
		return v;
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

gb_internal fbValue fb_build_call_expr(fbBuilder *b, Ast *expr) {
	ast_node(ce, CallExpr, expr);

	// Build callee
	fbValue target = fb_build_expr(b, ce->proc);

	// Build arguments
	u32 aux_start = b->proc->aux_count;
	for_array(i, ce->args) {
		fbValue arg = fb_build_expr(b, ce->args[i]);
		fb_aux_push(b->proc, arg.id);
	}

	// Determine calling convention
	Type *proc_type = type_of_expr(ce->proc);
	if (proc_type != nullptr) {
		proc_type = base_type(proc_type);
	}
	bool is_odin_cc = false;
	if (proc_type != nullptr && proc_type->kind == Type_Proc) {
		is_odin_cc = (proc_type->Proc.calling_convention == ProcCC_Odin);
	}

	// Odin CC: append context pointer as last arg
	if (is_odin_cc && b->context_stack.count > 0) {
		fbContextData *ctx = &b->context_stack[b->context_stack.count - 1];
		fb_aux_push(b->proc, ctx->ctx.base.id);
	}

	u32 arg_count = b->proc->aux_count - aux_start;

	// Determine return type
	Type *result_type = nullptr;
	fbType ret_ft = FB_VOID;
	if (proc_type != nullptr && proc_type->kind == Type_Proc && proc_type->Proc.results != nullptr) {
		TypeTuple *results = &proc_type->Proc.results->Tuple;
		if (results->variables.count > 0) {
			if (is_odin_cc) {
				// Odin CC: last result is the return value.
				// Multi-return requires split-return support not yet implemented.
				GB_ASSERT_MSG(results->variables.count == 1,
					"fast backend: multi-return not yet supported (got %td results)",
					results->variables.count);
				result_type = results->variables[results->variables.count - 1]->type;
			} else {
				result_type = proc_type->Proc.results;
				if (result_type->kind == Type_Tuple && result_type->Tuple.variables.count == 1) {
					result_type = result_type->Tuple.variables[0]->type;
				}
			}
			ret_ft = fb_data_type(result_type);
		}
	}

	u32 r = fb_inst_emit(b->proc, FB_CALL, ret_ft, target.id, aux_start, arg_count, 0, 0);

	fbValue result = {};
	result.id = r;
	result.type = result_type;
	return result;
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
			return fb_emit_iconst(b, type, 0);
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

		GB_PANIC("fb_build_expr Ident: unresolved entity '%.*s' (kind=%d) in proc '%.*s'",
		LIT(e->token.string), e->kind, LIT(b->entity->token.string));
		return fb_value_nil();
	}

	case Ast_BinaryExpr:
		return fb_build_binary_expr(b, expr);

	case Ast_UnaryExpr: {
		ast_node(ue, UnaryExpr, expr);
		if (ue->op.kind == Token_And) {
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

	case Ast_CallExpr:
		return fb_build_call_expr(b, expr);

	case Ast_SelectorExpr:
	case Ast_IndexExpr:
	case Ast_DerefExpr:
		return fb_addr_load(b, fb_build_addr(b, expr));

	case Ast_Implicit:
		return fb_addr_load(b, fb_build_addr(b, expr));

	case Ast_Uninit: {
		u32 r = fb_inst_emit(b->proc, FB_UNDEF, fb_data_type(type), FB_NOREG, FB_NOREG, FB_NOREG, 0, 0);
		fbValue v = {};
		v.id = r;
		v.type = type;
		return v;
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

gb_internal void fb_scope_close(fbBuilder *b, fbDeferExitKind kind, u32 block) {
	// TODO: defer execution in Phase 6b
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

	// Build RHS values
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
			fb_addr_store(b, local, init);
		}
	}

	array_free(&inits);
}

gb_internal void fb_build_return_stmt(fbBuilder *b, Slice<Ast *> const &results) {
	Type *pt = base_type(b->type);
	GB_ASSERT(pt->kind == Type_Proc);

	if (results.count == 0) {
		fb_emit_ret_void(b);
		return;
	}

	// Single return value
	if (results.count == 1) {
		fbValue val = fb_build_expr(b, results[0]);

		// Convert to the actual return type
		TypeProc *proc_type = &pt->Proc;
		if (proc_type->results != nullptr) {
			TypeTuple *res = &proc_type->results->Tuple;
			bool is_odin_cc = (proc_type->calling_convention == ProcCC_Odin);
			Type *ret_type = nullptr;
			if (is_odin_cc && res->variables.count > 0) {
				ret_type = res->variables[res->variables.count - 1]->type;
			} else if (res->variables.count > 0) {
				ret_type = res->variables[0]->type;
			}
			if (ret_type != nullptr) {
				val = fb_emit_conv(b, val, ret_type);
			}
		}

		fb_emit_ret(b, val);
		return;
	}

	// Multi-return: just return the last value for now (Phase 6b for full support)
	fbValue last = fb_build_expr(b, results[results.count - 1]);
	fb_emit_ret(b, last);
}

gb_internal void fb_build_assign_stmt(fbBuilder *b, AstAssignStmt *as) {
	if (as->op.kind == Token_Eq) {
		// Simple assignment: build LHS addrs and RHS values, then store
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
		switch (as->op.kind) {
		case Token_AddEq: op = FB_ADD; break;
		case Token_SubEq: op = FB_SUB; break;
		case Token_MulEq: op = FB_MUL; break;
		case Token_QuoEq: op = fb_type_is_signed(type) ? FB_SDIV : FB_UDIV; break;
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
			fbValue notb = {};
			notb.id = not_r;
			notb.type = type;
			fbValue result = fb_emit_arith(b, FB_AND, old_val, notb, type);
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

	case Ast_BranchStmt: {
		ast_node(bs, BranchStmt, node);
		u32 target_block = 0;

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
		} else {
			for (fbTargetList *t = b->target_list; t != nullptr; t = t->prev) {
				if (t->is_block) continue;

				switch (bs->token.kind) {
				case Token_break:    target_block = t->break_block;    break;
				case Token_continue: target_block = t->continue_block; break;
				default: break;
				}
				if (target_block != 0) break;
			}
		}

		if (target_block != 0) {
			fb_emit_jump(b, target_block);
		}
		break;
	}

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
				u32 slot_idx = b->proc->param_locs[pi];
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
			if (!found) {
				// Parameter may be MEMORY class or ignored, skip for now
			}
		}
	}

	// Odin CC: register context pointer
	if (proc_type->calling_convention == ProcCC_Odin && b->proc->param_count > 0) {
		// Context pointer is the last param slot
		u32 ctx_slot = b->proc->param_locs[b->proc->param_count - 1];
		fbStackSlot *slot = &b->proc->slots[ctx_slot];
		if (slot->entity == nullptr) {
			// This is the context pointer slot
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

	// Find __$startup_runtime proc index for entry point SYMADDR
	u32 startup_proc_idx = FB_NOREG;
	for_array(i, m->procs) {
		if (str_eq(m->procs[i]->name, str_lit("__$startup_runtime"))) {
			startup_proc_idx = cast(u32)i;
			break;
		}
	}

	// Determine which package the entry point belongs to.
	// Phase 6a only compiles procs in this package; all others get ret stubs.
	AstPackage *user_pkg = info->entry_point ? info->entry_point->pkg : nullptr;

	// Second pass: generate IR from AST for non-foreign, non-stub procedures
	for_array(i, m->procs) {
		fbProc *p = m->procs[i];
		if (p->is_foreign) continue;
		if (p->inst_count > 0) continue; // skip stubs already populated

		bool is_entry = (p->entity == info->entry_point);
		bool is_user_pkg = (p->entity != nullptr && p->entity->pkg == user_pkg);

		if (is_entry && startup_proc_idx != FB_NOREG) {
			// Entry point: synthetic IR — SYMADDR + CALL startup_runtime + RET 0
			// The runtime can't be compiled yet, so we keep synthetic IR for the entry
			u32 bb0 = fb_block_create(p);
			fb_block_start(p, bb0);
			u32 sym = fb_inst_emit(p, FB_SYMADDR, FB_PTR, FB_NOREG, FB_NOREG, FB_NOREG, 0, cast(i64)startup_proc_idx);
			fb_inst_emit(p, FB_CALL, FB_VOID, sym, p->aux_count, 0, 0, 0);
			u32 zero = fb_inst_emit(p, FB_ICONST, FB_I64, FB_NOREG, FB_NOREG, FB_NOREG, 0, 0);
			fb_inst_emit(p, FB_RET, FB_VOID, zero, FB_NOREG, FB_NOREG, 0, 0);
			continue;
		}

		// Phase 6a: only compile procs from the user's package.
		// Runtime procs use builtins, slices, maps, etc. that aren't supported yet.
		if (!is_user_pkg) {
			u32 bb0 = fb_block_create(p);
			fb_block_start(p, bb0);
			fb_inst_emit(p, FB_RET, FB_VOID, FB_NOREG, FB_NOREG, FB_NOREG, 0, 0);
			continue;
		}

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

		fb_procedure_generate(&b);

		// Cleanup builder
		array_free(&b.scope_stack);
		array_free(&b.context_stack);
		array_free(&b.defer_stack);
		array_free(&b.branch_regions);
		map_destroy(&b.variable_map);
		map_destroy(&b.soa_values_map);
	}
}
