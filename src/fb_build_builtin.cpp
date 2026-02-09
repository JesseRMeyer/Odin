// Fast Backend — Built-in procedure handling
//
// Phase 6b: implements Odin built-in procedures (len, cap, min, max, etc.)
// that map to IR primitives or small instruction sequences.
//
// Compile-time-constant builtins (size_of, align_of, offset_of, len on arrays)
// are handled by the constant folding at the top of fb_build_expr.
// This file handles the runtime cases.

// ───────────────────────────────────────────────────────────────────────
// Container field helpers: len, cap, raw_data
// ───────────────────────────────────────────────────────────────────────

// fb_load_field is defined in fb_build.cpp (shared with slice expression builder)

gb_internal fbValue fb_builtin_len(fbBuilder *b, Ast *arg_expr) {
	Type *t = base_type(type_of_expr(arg_expr));

	// Pointer to container: dereference first, then access fields
	if (is_type_pointer(t)) {
		fbValue ptr = fb_build_expr(b, arg_expr);
		t = base_type(type_deref(type_of_expr(arg_expr)));
		i64 len_offset = build_context.ptr_size; // len follows the data pointer
		return fb_load_field(b, ptr, len_offset, t_int);
	}

	switch (t->kind) {
	case Type_Array:
		return fb_emit_iconst(b, t_int, t->Array.count);
	case Type_EnumeratedArray:
		return fb_emit_iconst(b, t_int, t->EnumeratedArray.count);
	case Type_Slice:
	case Type_DynamicArray: {
		// Slice:   {data: rawptr, len: int}            → len at ptr_size
		// DynArr:  {data: rawptr, len: int, cap: int, alloc: Allocator} → len at ptr_size
		fbAddr addr = fb_build_addr(b, arg_expr);
		return fb_load_field(b, addr.base, build_context.ptr_size, t_int);
	}
	case Type_Basic:
		if (is_type_string(t)) {
			// string: {data: [^]u8, len: int} → len at ptr_size
			fbAddr addr = fb_build_addr(b, arg_expr);
			return fb_load_field(b, addr.base, build_context.ptr_size, t_int);
		}
		break;
	case Type_Map: {
		// raw_map: {data: uintptr, len: uintptr, allocator: Allocator}
		// len is field 1 at ptr_size
		fbAddr addr = fb_build_addr(b, arg_expr);
		fbValue raw_len = fb_load_field(b, addr.base, build_context.ptr_size, t_uintptr);
		return fb_emit_conv(b, raw_len, t_int);
	}
	case Type_Struct:
		if (is_type_soa_struct(t)) {
			if (t->Struct.soa_kind == StructSoa_Fixed) {
				return fb_emit_iconst(b, t_int, t->Struct.soa_count);
			}
		}
		break;
	default:
		break;
	}

	GB_PANIC("fb_builtin_len: unhandled type %s", type_to_string(t));
	return fb_value_nil();
}

gb_internal fbValue fb_builtin_cap(fbBuilder *b, Ast *arg_expr) {
	Type *t = base_type(type_of_expr(arg_expr));

	if (is_type_pointer(t)) {
		fbValue ptr = fb_build_expr(b, arg_expr);
		t = base_type(type_deref(type_of_expr(arg_expr)));
		if (t->kind == Type_DynamicArray) {
			return fb_load_field(b, ptr, build_context.ptr_size + build_context.int_size, t_int);
		}
		// Slice and string cap == len
		return fb_load_field(b, ptr, build_context.ptr_size, t_int);
	}

	switch (t->kind) {
	case Type_Array:
		return fb_emit_iconst(b, t_int, t->Array.count);
	case Type_EnumeratedArray:
		return fb_emit_iconst(b, t_int, t->EnumeratedArray.count);
	case Type_Slice: {
		// Slice has no separate cap; cap(slice) == len(slice) in Odin
		fbAddr addr = fb_build_addr(b, arg_expr);
		return fb_load_field(b, addr.base, build_context.ptr_size, t_int);
	}
	case Type_DynamicArray: {
		// DynArr: cap is field 2 at ptr_size + int_size
		fbAddr addr = fb_build_addr(b, arg_expr);
		return fb_load_field(b, addr.base, build_context.ptr_size + build_context.int_size, t_int);
	}
	case Type_Basic:
		if (is_type_string(t)) {
			// cap(string) == len(string)
			fbAddr addr = fb_build_addr(b, arg_expr);
			return fb_load_field(b, addr.base, build_context.ptr_size, t_int);
		}
		break;
	default:
		break;
	}

	GB_PANIC("fb_builtin_cap: unhandled type %s", type_to_string(t));
	return fb_value_nil();
}

gb_internal fbValue fb_builtin_raw_data(fbBuilder *b, Ast *arg_expr) {
	Type *t = base_type(type_of_expr(arg_expr));

	switch (t->kind) {
	case Type_Slice:
	case Type_DynamicArray: {
		// Data pointer is field 0, at offset 0
		fbAddr addr = fb_build_addr(b, arg_expr);
		return fb_emit_load(b, addr.base, t_rawptr);
	}
	case Type_Basic:
		if (t->Basic.kind == Basic_string) {
			fbAddr addr = fb_build_addr(b, arg_expr);
			return fb_emit_load(b, addr.base, t_rawptr);
		}
		if (t->Basic.kind == Basic_cstring) {
			fbValue val = fb_build_expr(b, arg_expr);
			return fb_emit_conv(b, val, t_rawptr);
		}
		break;
	case Type_Pointer:
		if (is_type_array_like(t->Pointer.elem)) {
			return fb_build_expr(b, arg_expr);
		}
		break;
	case Type_MultiPointer:
		return fb_build_expr(b, arg_expr);
	default:
		break;
	}

	GB_PANIC("fb_builtin_raw_data: unhandled type %s", type_to_string(t));
	return fb_value_nil();
}

// ───────────────────────────────────────────────────────────────────────
// Arithmetic builtins: min, max, abs, clamp
// ───────────────────────────────────────────────────────────────────────

gb_internal fbValue fb_builtin_min(fbBuilder *b, Type *t, fbValue x, fbValue y) {
	x = fb_emit_conv(b, x, t);
	y = fb_emit_conv(b, y, t);

	bool is_float = fb_type_is_float(fb_data_type(t));
	fbOp cmp_op;
	if (is_float) {
		cmp_op = FB_CMP_FLT;
	} else {
		cmp_op = fb_type_is_signed(t) ? FB_CMP_SLT : FB_CMP_ULT;
	}
	fbValue cond = fb_emit_cmp(b, cmp_op, x, y);
	return fb_emit_select(b, cond, x, y, t);
}

gb_internal fbValue fb_builtin_max(fbBuilder *b, Type *t, fbValue x, fbValue y) {
	x = fb_emit_conv(b, x, t);
	y = fb_emit_conv(b, y, t);

	bool is_float = fb_type_is_float(fb_data_type(t));
	fbOp cmp_op;
	if (is_float) {
		cmp_op = FB_CMP_FGT;
	} else {
		cmp_op = fb_type_is_signed(t) ? FB_CMP_SGT : FB_CMP_UGT;
	}
	fbValue cond = fb_emit_cmp(b, cmp_op, x, y);
	return fb_emit_select(b, cond, x, y, t);
}

gb_internal fbValue fb_builtin_abs(fbBuilder *b, fbValue x) {
	Type *t = x.type;
	if (is_type_unsigned(t)) {
		return x;
	}

	fbType ft = fb_data_type(t);
	bool is_float = fb_type_is_float(ft);

	fbValue zero;
	if (is_float) {
		zero = fb_emit_fconst(b, t, 0.0);
	} else {
		zero = fb_emit_iconst(b, t, 0);
	}

	fbOp cmp_op = is_float ? FB_CMP_FLT : FB_CMP_SLT;
	fbValue cond = fb_emit_cmp(b, cmp_op, x, zero);

	fbOp neg_op = is_float ? FB_FNEG : FB_NEG;
	u32 neg_r = fb_inst_emit(b->proc, neg_op, ft, x.id, FB_NOREG, FB_NOREG, 0, 0);
	fbValue neg = {};
	neg.id = neg_r;
	neg.type = t;

	return fb_emit_select(b, cond, neg, x, t);
}

gb_internal fbValue fb_builtin_clamp(fbBuilder *b, Type *t, fbValue x, fbValue lo, fbValue hi) {
	fbValue z = fb_builtin_max(b, t, x, lo);
	return fb_builtin_min(b, t, z, hi);
}

// ───────────────────────────────────────────────────────────────────────
// Atomic builtins
// ───────────────────────────────────────────────────────────────────────

gb_internal u8 fb_atomic_order_from_odin(Ast *expr) {
	ExactValue value = type_and_value_of_expr(expr).value;
	return cast(u8)exact_value_to_i64(value);
}

gb_internal fbValue fb_build_atomic_builtin(fbBuilder *b, Ast *expr, TypeAndValue const &tv, BuiltinProcId id) {
	ast_node(ce, CallExpr, expr);
	Type *type = type_of_expr(expr);

	switch (id) {
	case BuiltinProc_atomic_type_is_lock_free:
		// On x86-64, aligned loads/stores up to 8 bytes are lock-free
		return fb_emit_iconst(b, t_bool, 1);

	case BuiltinProc_atomic_thread_fence: {
		u8 order = fb_atomic_order_from_odin(ce->args[0]);
		fb_inst_emit(b->proc, FB_FENCE, FB_VOID, FB_NOREG, FB_NOREG, FB_NOREG, 0, cast(i64)order);
		return fb_value_nil();
	}

	case BuiltinProc_atomic_signal_fence: {
		// Signal fence is a compiler barrier only — no hardware fence on x86-64.
		// Emit FB_FENCE with a special flag (bit 3) to mark it as signal-only.
		u8 order = fb_atomic_order_from_odin(ce->args[0]);
		fb_inst_emit(b->proc, FB_FENCE, FB_VOID, FB_NOREG, FB_NOREG, FB_NOREG, 0, cast(i64)(order | 0x08));
		return fb_value_nil();
	}

	case BuiltinProc_atomic_load:
	case BuiltinProc_atomic_load_explicit: {
		fbValue ptr = fb_build_expr(b, ce->args[0]);
		Type *elem = type_deref(type_of_expr(ce->args[0]));
		fbType ft = fb_data_type(elem);
		if (ft.kind == FBT_VOID) ft = FB_I64;

		u8 order = OdinAtomicMemoryOrder_seq_cst;
		if (id == BuiltinProc_atomic_load_explicit) {
			order = fb_atomic_order_from_odin(ce->args[1]);
		}

		u32 r = fb_inst_emit(b->proc, FB_ATOMIC_LOAD, ft, ptr.id, FB_NOREG, FB_NOREG, 0, 0);
		b->proc->insts[b->proc->inst_count - 1].flags = order & FBF_ORDER_MASK;
		return fb_make_value(r, elem);
	}

	case BuiltinProc_atomic_store:
	case BuiltinProc_atomic_store_explicit: {
		fbValue ptr = fb_build_expr(b, ce->args[0]);
		fbValue val = fb_build_expr(b, ce->args[1]);
		Type *elem = type_deref(type_of_expr(ce->args[0]));
		val = fb_emit_conv(b, val, elem);

		fbType ft = fb_data_type(elem);
		if (ft.kind == FBT_VOID) ft = FB_I64;

		u8 order = OdinAtomicMemoryOrder_seq_cst;
		if (id == BuiltinProc_atomic_store_explicit) {
			order = fb_atomic_order_from_odin(ce->args[2]);
		}

		fb_inst_emit(b->proc, FB_ATOMIC_STORE, ft, ptr.id, val.id, FB_NOREG, 0, 0);
		b->proc->insts[b->proc->inst_count - 1].flags = order & FBF_ORDER_MASK;
		return fb_value_nil();
	}

	case BuiltinProc_atomic_add:
	case BuiltinProc_atomic_sub:
	case BuiltinProc_atomic_and:
	case BuiltinProc_atomic_or:
	case BuiltinProc_atomic_xor:
	case BuiltinProc_atomic_exchange:
	case BuiltinProc_atomic_add_explicit:
	case BuiltinProc_atomic_sub_explicit:
	case BuiltinProc_atomic_and_explicit:
	case BuiltinProc_atomic_or_explicit:
	case BuiltinProc_atomic_xor_explicit:
	case BuiltinProc_atomic_exchange_explicit: {
		fbValue ptr = fb_build_expr(b, ce->args[0]);
		fbValue val = fb_build_expr(b, ce->args[1]);
		Type *elem = type_deref(type_of_expr(ce->args[0]));
		val = fb_emit_conv(b, val, elem);

		fbType ft = fb_data_type(elem);
		if (ft.kind == FBT_VOID) ft = FB_I64;

		fbOp op;
		u8 order = OdinAtomicMemoryOrder_seq_cst;
		switch (id) {
		case BuiltinProc_atomic_add:      op = FB_ATOMIC_ADD;  break;
		case BuiltinProc_atomic_sub:      op = FB_ATOMIC_SUB;  break;
		case BuiltinProc_atomic_and:      op = FB_ATOMIC_AND;  break;
		case BuiltinProc_atomic_or:       op = FB_ATOMIC_OR;   break;
		case BuiltinProc_atomic_xor:      op = FB_ATOMIC_XOR;  break;
		case BuiltinProc_atomic_exchange:  op = FB_ATOMIC_XCHG; break;
		case BuiltinProc_atomic_add_explicit:
			op = FB_ATOMIC_ADD;  order = fb_atomic_order_from_odin(ce->args[2]); break;
		case BuiltinProc_atomic_sub_explicit:
			op = FB_ATOMIC_SUB;  order = fb_atomic_order_from_odin(ce->args[2]); break;
		case BuiltinProc_atomic_and_explicit:
			op = FB_ATOMIC_AND;  order = fb_atomic_order_from_odin(ce->args[2]); break;
		case BuiltinProc_atomic_or_explicit:
			op = FB_ATOMIC_OR;   order = fb_atomic_order_from_odin(ce->args[2]); break;
		case BuiltinProc_atomic_xor_explicit:
			op = FB_ATOMIC_XOR;  order = fb_atomic_order_from_odin(ce->args[2]); break;
		case BuiltinProc_atomic_exchange_explicit:
			op = FB_ATOMIC_XCHG; order = fb_atomic_order_from_odin(ce->args[2]); break;
		default: GB_PANIC("unreachable"); op = FB_ATOMIC_ADD; break;
		}

		u32 r = fb_inst_emit(b->proc, op, ft, ptr.id, val.id, FB_NOREG, 0, 0);
		b->proc->insts[b->proc->inst_count - 1].flags = order & FBF_ORDER_MASK;
		return fb_make_value(r, elem);
	}

	case BuiltinProc_atomic_nand:
	case BuiltinProc_atomic_nand_explicit: {
		// NAND: old = *ptr; *ptr = ~(old & val); return old
		// Implement as a CAS loop since there's no atomic NAND instruction
		fbValue ptr = fb_build_expr(b, ce->args[0]);
		fbValue val = fb_build_expr(b, ce->args[1]);
		Type *elem = type_deref(type_of_expr(ce->args[0]));
		val = fb_emit_conv(b, val, elem);

		fbType ft = fb_data_type(elem);
		if (ft.kind == FBT_VOID) ft = FB_I64;

		u8 order = OdinAtomicMemoryOrder_seq_cst;
		if (id == BuiltinProc_atomic_nand_explicit) {
			order = fb_atomic_order_from_odin(ce->args[2]);
		}

		// Load current value
		u32 loop_blk = fb_new_block(b);
		u32 done_blk = fb_new_block(b);
		fb_emit_jump(b, loop_blk);
		fb_set_block(b, loop_blk);

		u32 old_r = fb_inst_emit(b->proc, FB_ATOMIC_LOAD, ft, ptr.id, FB_NOREG, FB_NOREG, 0, 0);
		b->proc->insts[b->proc->inst_count - 1].flags = order & FBF_ORDER_MASK;
		fbValue old_val = fb_make_value(old_r, elem);

		// Compute ~(old & val)
		fbValue and_val = fb_emit_arith(b, FB_AND, old_val, val, elem);
		u32 not_r = fb_inst_emit(b->proc, FB_NOT, ft, and_val.id, FB_NOREG, FB_NOREG, 0, 0);
		fbValue new_val = fb_make_value(not_r, elem);

		// CAS: try to swap old → new
		u32 cas_r = fb_inst_emit(b->proc, FB_ATOMIC_CAS, ft, ptr.id, old_val.id, new_val.id, 0, 0);
		b->proc->insts[b->proc->inst_count - 1].flags = (order & FBF_ORDER_MASK) | ((order & FBF_ORDER_MASK) << FBF_FAIL_ORDER_SHIFT);

		// CAS returns old value; succeeded if cas_result == expected
		fbValue cas_val = fb_make_value(cas_r, elem);
		fbValue succeeded = fb_emit_cmp(b, FB_CMP_EQ, cas_val, old_val);
		fb_emit_branch(b, succeeded, done_blk, loop_blk);

		fb_set_block(b, done_blk);
		return old_val;
	}

	case BuiltinProc_atomic_compare_exchange_strong:
	case BuiltinProc_atomic_compare_exchange_weak:
	case BuiltinProc_atomic_compare_exchange_strong_explicit:
	case BuiltinProc_atomic_compare_exchange_weak_explicit: {
		fbValue ptr = fb_build_expr(b, ce->args[0]);
		fbValue expected = fb_build_expr(b, ce->args[1]);
		fbValue desired = fb_build_expr(b, ce->args[2]);
		Type *elem = type_deref(type_of_expr(ce->args[0]));
		expected = fb_emit_conv(b, expected, elem);
		desired = fb_emit_conv(b, desired, elem);

		fbType ft = fb_data_type(elem);
		if (ft.kind == FBT_VOID) ft = FB_I64;

		u8 success_order = OdinAtomicMemoryOrder_seq_cst;
		u8 failure_order = OdinAtomicMemoryOrder_seq_cst;
		if (id == BuiltinProc_atomic_compare_exchange_strong_explicit ||
		    id == BuiltinProc_atomic_compare_exchange_weak_explicit) {
			success_order = fb_atomic_order_from_odin(ce->args[3]);
			failure_order = fb_atomic_order_from_odin(ce->args[4]);
		}

		u32 cas_r = fb_inst_emit(b->proc, FB_ATOMIC_CAS, ft, ptr.id, expected.id, desired.id, 0, 0);
		b->proc->insts[b->proc->inst_count - 1].flags =
			(success_order & FBF_ORDER_MASK) | ((failure_order & FBF_ORDER_MASK) << FBF_FAIL_ORDER_SHIFT);
		fbValue cas_val = fb_make_value(cas_r, elem);

		if (is_type_tuple(tv.type)) {
			// Returns (old_value, bool)
			fbValue succeeded = fb_emit_cmp(b, FB_CMP_EQ, cas_val, expected);

			fbAddr res = fb_add_local(b, tv.type, nullptr, false);
			i64 off0 = type_offset_of(tv.type, 0);
			i64 off1 = type_offset_of(tv.type, 1);

			fbValue ptr0 = res.base;
			if (off0 != 0) ptr0 = fb_emit_member(b, res.base, off0);
			fb_emit_store(b, ptr0, cas_val);

			fbValue ptr1 = fb_emit_member(b, res.base, off1);
			fb_emit_store(b, ptr1, succeeded);

			fbValue ret = res.base;
			ret.type = tv.type;
			return ret;
		} else {
			return cas_val;
		}
	}

	default:
		break;
	}

	GB_PANIC("fast backend: unhandled atomic builtin '%.*s' (id=%d)",
		LIT(builtin_procs[id].name), id);
	return fb_value_nil();
}

// ───────────────────────────────────────────────────────────────────────
// SIMD builtins
// ───────────────────────────────────────────────────────────────────────

gb_internal fbValue fb_build_simd_builtin(fbBuilder *b, Ast *expr, TypeAndValue const &tv, BuiltinProcId id) {
	ast_node(ce, CallExpr, expr);
	Type *type = type_of_expr(expr);
	Type *bt = base_type(type);

	switch (id) {
	// ── Lane-wise arithmetic ─────────────────────────────────────
	case BuiltinProc_simd_add:
	case BuiltinProc_simd_sub:
	case BuiltinProc_simd_mul: {
		fbValue a = fb_build_expr(b, ce->args[0]);
		fbValue b_ = fb_build_expr(b, ce->args[1]);
		Type *elem = base_type(type)->SimdVector.elem;
		bool is_float = is_type_float(elem);

		fbOp op;
		switch (id) {
		case BuiltinProc_simd_add: op = is_float ? FB_FADD : FB_ADD; break;
		case BuiltinProc_simd_sub: op = is_float ? FB_FSUB : FB_SUB; break;
		case BuiltinProc_simd_mul: op = is_float ? FB_FMUL : FB_MUL; break;
		default: GB_PANIC("unreachable"); op = FB_ADD; break;
		}
		return fb_emit_arith(b, op, a, b_, type);
	}

	// ── Lane-wise bitwise ────────────────────────────────────────
	case BuiltinProc_simd_bit_and:
	case BuiltinProc_simd_bit_or:
	case BuiltinProc_simd_bit_xor: {
		fbValue a = fb_build_expr(b, ce->args[0]);
		fbValue b_ = fb_build_expr(b, ce->args[1]);

		fbOp op;
		switch (id) {
		case BuiltinProc_simd_bit_and: op = FB_AND; break;
		case BuiltinProc_simd_bit_or:  op = FB_OR;  break;
		case BuiltinProc_simd_bit_xor: op = FB_XOR; break;
		default: GB_PANIC("unreachable"); op = FB_XOR; break;
		}
		return fb_emit_arith(b, op, a, b_, type);
	}

	case BuiltinProc_simd_bit_and_not: {
		fbValue a = fb_build_expr(b, ce->args[0]);
		fbValue b_ = fb_build_expr(b, ce->args[1]);
		// a & ~b  →  PANDN in SSE2 (b_not = NOT b, result = AND a, b_not)
		fbType ft = fb_data_type(type);
		fbValue b_not;
		b_not.id = fb_inst_emit(b->proc, FB_NOT, ft, b_.id, FB_NOREG, FB_NOREG, 0, 0);
		b_not.type = type;
		return fb_emit_arith(b, FB_AND, a, b_not, type);
	}

	case BuiltinProc_simd_bit_not: {
		fbValue a = fb_build_expr(b, ce->args[0]);
		fbType ft = fb_data_type(type);
		fbValue r;
		r.id = fb_inst_emit(b->proc, FB_NOT, ft, a.id, FB_NOREG, FB_NOREG, 0, 0);
		r.type = type;
		return r;
	}

	// ── Lane-wise shifts ─────────────────────────────────────────
	// SSE2 PSLLD/PSRLD/PSRAD use a single shift count from the low
	// 64 bits of the source operand. For uniform shift vectors (all
	// lanes same value), we extract the scalar count and store it in
	// imm, then the lowerer can use the immediate form directly.
	case BuiltinProc_simd_shl:
	case BuiltinProc_simd_shr:
	case BuiltinProc_simd_shl_masked:
	case BuiltinProc_simd_shr_masked: {
		fbValue a = fb_build_expr(b, ce->args[0]);
		Type *elem = bt->SimdVector.elem;
		bool is_signed = is_type_integer(elem) && !is_type_unsigned(elem);

		fbOp op;
		if (id == BuiltinProc_simd_shl || id == BuiltinProc_simd_shl_masked) {
			op = FB_SHL;
		} else {
			op = is_signed ? FB_ASHR : FB_LSHR;
		}

		// Try to extract compile-time constant shift amount from the
		// shift vector argument (handles both scalar and splat vector).
		TypeAndValue shift_tv = type_and_value_of_expr(ce->args[1]);
		i64 shift_amount = -1;
		if (shift_tv.value.kind != ExactValue_Invalid) {
			shift_amount = exact_value_to_i64(shift_tv.value);
		}

		fbType ft = fb_data_type(type);
		if (shift_amount >= 0) {
			// Constant shift: store in imm field. Lowerer uses PSLLD/PSRLD imm8.
			// For Odin semantics: if shift >= bit_width, PSLLD already zeros.
			fbValue r;
			r.id = fb_inst_emit(b->proc, op, ft, a.id, FB_NOREG, FB_NOREG, 0, shift_amount);
			r.type = type;
			return r;
		}

		// Non-constant: build shift vector, extract lane 0, use as scalar.
		fbValue b_ = fb_build_expr(b, ce->args[1]);
		fbValue r;
		r.id = fb_inst_emit(b->proc, op, ft, a.id, b_.id, FB_NOREG, 0, 0);
		r.type = type;
		return r;
	}

	// ── Extract / Replace / Shuffle ──────────────────────────────
	case BuiltinProc_simd_extract: {
		fbValue vec = fb_build_expr(b, ce->args[0]);
		// Lane index is a compile-time constant
		TypeAndValue idx_tv = type_and_value_of_expr(ce->args[1]);
		i64 lane = exact_value_to_i64(idx_tv.value);
		Type *elem = bt->SimdVector.elem;
		fbType ft = fb_data_type(elem);
		fbValue r;
		r.id = fb_inst_emit(b->proc, FB_VEXTRACT, ft, vec.id, FB_NOREG, FB_NOREG, 0, lane);
		r.type = elem;
		return r;
	}

	case BuiltinProc_simd_replace: {
		fbValue vec = fb_build_expr(b, ce->args[0]);
		TypeAndValue idx_tv = type_and_value_of_expr(ce->args[1]);
		i64 lane = exact_value_to_i64(idx_tv.value);
		fbValue val = fb_build_expr(b, ce->args[2]);
		fbType ft = fb_data_type(type);
		fbValue r;
		r.id = fb_inst_emit(b->proc, FB_VINSERT, ft, vec.id, val.id, FB_NOREG, 0, lane);
		r.type = type;
		return r;
	}

	// ── Lane-wise comparison ─────────────────────────────────────
	case BuiltinProc_simd_lanes_eq:
	case BuiltinProc_simd_lanes_ne:
	case BuiltinProc_simd_lanes_lt:
	case BuiltinProc_simd_lanes_le:
	case BuiltinProc_simd_lanes_gt:
	case BuiltinProc_simd_lanes_ge: {
		fbValue a = fb_build_expr(b, ce->args[0]);
		fbValue b_ = fb_build_expr(b, ce->args[1]);
		Type *arg_type = type_of_expr(ce->args[0]);
		Type *arg_bt = base_type(arg_type);
		Type *elem = arg_bt->SimdVector.elem;
		bool is_signed_int = is_type_integer(elem) && !is_type_unsigned(elem);
		bool is_float_elem = is_type_float(elem);

		fbOp cmp_op;
		switch (id) {
		case BuiltinProc_simd_lanes_eq: cmp_op = is_float_elem ? FB_CMP_FEQ : FB_CMP_EQ; break;
		case BuiltinProc_simd_lanes_ne: cmp_op = is_float_elem ? FB_CMP_FNE : FB_CMP_NE; break;
		case BuiltinProc_simd_lanes_lt: cmp_op = is_float_elem ? FB_CMP_FLT : (is_signed_int ? FB_CMP_SLT : FB_CMP_ULT); break;
		case BuiltinProc_simd_lanes_le: cmp_op = is_float_elem ? FB_CMP_FLE : (is_signed_int ? FB_CMP_SLE : FB_CMP_ULE); break;
		case BuiltinProc_simd_lanes_gt: cmp_op = is_float_elem ? FB_CMP_FGT : (is_signed_int ? FB_CMP_SGT : FB_CMP_UGT); break;
		case BuiltinProc_simd_lanes_ge: cmp_op = is_float_elem ? FB_CMP_FGE : (is_signed_int ? FB_CMP_SGE : FB_CMP_UGE); break;
		default: GB_PANIC("unreachable"); cmp_op = FB_CMP_EQ; break;
		}

		fbType ft = fb_data_type(type);
		fbValue r;
		r.id = fb_inst_emit(b->proc, cmp_op, ft, a.id, b_.id, FB_NOREG, 0, 0);
		r.type = type;
		return r;
	}

	// ── Reductions ───────────────────────────────────────────────
	case BuiltinProc_simd_reduce_or: {
		fbValue a = fb_build_expr(b, ce->args[0]);
		Type *arg_type = type_of_expr(ce->args[0]);
		fbType src_ft = fb_data_type(arg_type);
		fbType dst_ft = fb_data_type(type);
		// Horizontal OR reduction: extract to scalar via a new opcode
		// We use FB_VEXTRACT with lane=-1 as a convention for "reduce_or"
		fbValue r;
		r.id = fb_inst_emit(b->proc, FB_VEXTRACT, dst_ft, a.id, FB_NOREG, FB_NOREG, 0, -1);
		r.type = type;
		return r;
	}

	case BuiltinProc_simd_reduce_min: {
		fbValue a = fb_build_expr(b, ce->args[0]);
		fbType dst_ft = fb_data_type(type);
		// Horizontal MIN reduction: use lane=-2 convention
		fbValue r;
		r.id = fb_inst_emit(b->proc, FB_VEXTRACT, dst_ft, a.id, FB_NOREG, FB_NOREG, 0, -2);
		r.type = type;
		return r;
	}

	// ── Select (blend) ───────────────────────────────────────────
	case BuiltinProc_simd_select: {
		// simd_select(mask, true_val, false_val)
		fbValue mask = fb_build_expr(b, ce->args[0]);
		fbValue t_val = fb_build_expr(b, ce->args[1]);
		fbValue f_val = fb_build_expr(b, ce->args[2]);
		fbType ft = fb_data_type(type);
		fbValue r;
		r.id = fb_inst_emit(b->proc, FB_SELECT, ft, mask.id, t_val.id, f_val.id, 0, 0);
		r.type = type;
		return r;
	}

	// ── Indices (iota) ───────────────────────────────────────────
	case BuiltinProc_simd_indices: {
		// Returns a vector {0, 1, 2, ..., N-1}
		// Build as a compound literal on the stack
		i64 count = bt->SimdVector.count;
		Type *elem = bt->SimdVector.elem;
		i64 elem_size = type_size_of(elem);
		fbAddr v = fb_add_local(b, type, nullptr, false);
		for (i64 i = 0; i < count; i++) {
			fbValue val = fb_emit_iconst(b, elem, i);
			fbValue dst = v.base;
			if (i > 0) dst = fb_emit_member(b, v.base, i * elem_size);
			fb_emit_store(b, dst, val);
		}
		return fb_addr_load(b, v);
	}

	// ── Neg ──────────────────────────────────────────────────────
	case BuiltinProc_simd_neg: {
		fbValue a = fb_build_expr(b, ce->args[0]);
		Type *elem = bt->SimdVector.elem;
		bool is_float_elem = is_type_float(elem);
		fbType ft = fb_data_type(type);
		fbValue r;
		r.id = fb_inst_emit(b->proc, is_float_elem ? FB_FNEG : FB_NEG, ft, a.id, FB_NOREG, FB_NOREG, 0, 0);
		r.type = type;
		return r;
	}

	default:
		GB_PANIC("fast backend: unhandled SIMD builtin '%.*s' (id=%d)",
			LIT(builtin_procs[id].name), id);
		return fb_value_nil();
	}
}

// ───────────────────────────────────────────────────────────────────────
// Main dispatch
// ───────────────────────────────────────────────────────────────────────

gb_internal fbValue fb_build_builtin_proc(fbBuilder *b, Ast *expr, TypeAndValue const &tv, BuiltinProcId id) {
	ast_node(ce, CallExpr, expr);
	Type *type = type_of_expr(expr);

	// SIMD builtins
	if (BuiltinProc__simd_begin < id && id < BuiltinProc__simd_end) {
		return fb_build_simd_builtin(b, expr, tv, id);
	}

	// Atomic builtins
	if (BuiltinProc__atomic_begin < id && id < BuiltinProc__atomic_end) {
		return fb_build_atomic_builtin(b, expr, tv, id);
	}

	// Type query builtins should all be compile-time constants,
	// caught by the constant folding at the top of fb_build_expr.
	if (BuiltinProc__type_begin < id && id < BuiltinProc__type_end) {
		GB_PANIC("fast backend: type query builtin %d was not constant-folded", id);
	}

	switch (id) {
	case BuiltinProc_DIRECTIVE:
		// #location, #load etc. - unhandled for now
		GB_PANIC("fast backend: #directive builtins not yet supported");
		return fb_value_nil();

	// ── Container introspection ──────────────────────────────────

	case BuiltinProc_len: {
		return fb_builtin_len(b, ce->args[0]);
	}

	case BuiltinProc_cap: {
		return fb_builtin_cap(b, ce->args[0]);
	}

	case BuiltinProc_raw_data: {
		return fb_builtin_raw_data(b, ce->args[0]);
	}

	// ── Arithmetic ───────────────────────────────────────────────

	case BuiltinProc_min: {
		Type *t = type_of_expr(expr);
		fbValue x = fb_build_expr(b, ce->args[0]);
		for (isize i = 1; i < ce->args.count; i++) {
			fbValue y = fb_build_expr(b, ce->args[i]);
			x = fb_builtin_min(b, t, x, y);
		}
		return x;
	}

	case BuiltinProc_max: {
		Type *t = type_of_expr(expr);
		fbValue x = fb_build_expr(b, ce->args[0]);
		for (isize i = 1; i < ce->args.count; i++) {
			fbValue y = fb_build_expr(b, ce->args[i]);
			x = fb_builtin_max(b, t, x, y);
		}
		return x;
	}

	case BuiltinProc_abs: {
		fbValue x = fb_build_expr(b, ce->args[0]);
		return fb_builtin_abs(b, x);
	}

	case BuiltinProc_clamp: {
		Type *t = type_of_expr(expr);
		fbValue x  = fb_build_expr(b, ce->args[0]);
		fbValue lo = fb_build_expr(b, ce->args[1]);
		fbValue hi = fb_build_expr(b, ce->args[2]);
		return fb_builtin_clamp(b, t, x, lo, hi);
	}

	// ── Overflow arithmetic ─────────────────────────────────────

	case BuiltinProc_overflow_add: {
		Type *main_type = tv.type;
		Type *elem_type = main_type;
		if (is_type_tuple(main_type)) {
			elem_type = main_type->Tuple.variables[0]->type;
		}

		fbValue x = fb_build_expr(b, ce->args[0]);
		fbValue y = fb_build_expr(b, ce->args[1]);
		x = fb_emit_conv(b, x, elem_type);
		y = fb_emit_conv(b, y, elem_type);

		fbValue result = fb_emit_arith(b, FB_ADD, x, y, elem_type);

		if (!is_type_tuple(main_type)) {
			// Single-value context: discard overflow flag
			return result;
		}

		// Overflow detection
		fbValue overflow;
		if (is_type_unsigned(elem_type)) {
			// Unsigned: overflow iff result < a (wrapping)
			overflow = fb_emit_cmp(b, FB_CMP_ULT, result, x);
		} else {
			// Signed: overflow iff (a ^ result) & (b ^ result) has sign bit set
			fbValue xor_ar = fb_emit_arith(b, FB_XOR, x, result, elem_type);
			fbValue xor_br = fb_emit_arith(b, FB_XOR, y, result, elem_type);
			fbValue sign   = fb_emit_arith(b, FB_AND, xor_ar, xor_br, elem_type);
			fbValue zero   = fb_emit_iconst(b, elem_type, 0);
			overflow = fb_emit_cmp(b, FB_CMP_SLT, sign, zero);
		}

		// Pack into aggregate tuple (same pattern as type assertions)
		fbAddr res = fb_add_local(b, main_type, nullptr, false);
		i64 off0 = type_offset_of(main_type, 0);
		i64 off1 = type_offset_of(main_type, 1);

		fbValue ptr0 = res.base;
		if (off0 != 0) ptr0 = fb_emit_member(b, res.base, off0);
		fb_emit_store(b, ptr0, result);

		fbValue ptr1 = fb_emit_member(b, res.base, off1);
		fb_emit_store(b, ptr1, overflow);

		fbValue ret = res.base;
		ret.type = main_type;
		return ret;
	}

	case BuiltinProc_overflow_sub: {
		Type *main_type = tv.type;
		Type *elem_type = main_type;
		if (is_type_tuple(main_type)) {
			elem_type = main_type->Tuple.variables[0]->type;
		}

		fbValue x = fb_build_expr(b, ce->args[0]);
		fbValue y = fb_build_expr(b, ce->args[1]);
		x = fb_emit_conv(b, x, elem_type);
		y = fb_emit_conv(b, y, elem_type);

		fbValue result = fb_emit_arith(b, FB_SUB, x, y, elem_type);

		if (!is_type_tuple(main_type)) {
			return result;
		}

		fbValue overflow;
		if (is_type_unsigned(elem_type)) {
			// Unsigned: underflow iff result > a
			overflow = fb_emit_cmp(b, FB_CMP_UGT, result, x);
		} else {
			// Signed: overflow iff (a ^ b) & (a ^ result) has sign bit set
			fbValue xor_ab = fb_emit_arith(b, FB_XOR, x, y, elem_type);
			fbValue xor_ar = fb_emit_arith(b, FB_XOR, x, result, elem_type);
			fbValue sign   = fb_emit_arith(b, FB_AND, xor_ab, xor_ar, elem_type);
			fbValue zero   = fb_emit_iconst(b, elem_type, 0);
			overflow = fb_emit_cmp(b, FB_CMP_SLT, sign, zero);
		}

		fbAddr res = fb_add_local(b, main_type, nullptr, false);
		i64 off0 = type_offset_of(main_type, 0);
		i64 off1 = type_offset_of(main_type, 1);

		fbValue ptr0 = res.base;
		if (off0 != 0) ptr0 = fb_emit_member(b, res.base, off0);
		fb_emit_store(b, ptr0, result);

		fbValue ptr1 = fb_emit_member(b, res.base, off1);
		fb_emit_store(b, ptr1, overflow);

		fbValue ret = res.base;
		ret.type = main_type;
		return ret;
	}

	case BuiltinProc_overflow_mul: {
		Type *main_type = tv.type;
		Type *elem_type = main_type;
		if (is_type_tuple(main_type)) {
			elem_type = main_type->Tuple.variables[0]->type;
		}

		fbValue x = fb_build_expr(b, ce->args[0]);
		fbValue y = fb_build_expr(b, ce->args[1]);
		x = fb_emit_conv(b, x, elem_type);
		y = fb_emit_conv(b, y, elem_type);

		fbValue result = fb_emit_arith(b, FB_MUL, x, y, elem_type);

		if (!is_type_tuple(main_type)) {
			return result;
		}

		// Overflow detection: if y != 0 && result / y != x, overflow occurred.
		// For signed: use SDIV; for unsigned: use UDIV.
		fbValue zero = fb_emit_iconst(b, elem_type, 0);
		fbValue y_nonzero = fb_emit_cmp(b, FB_CMP_NE, y, zero);

		fbOp div_op = is_type_unsigned(elem_type) ? FB_UDIV : FB_SDIV;
		fbValue div_result = fb_emit_arith(b, div_op, result, y, elem_type);
		fbValue mismatch = fb_emit_cmp(b, FB_CMP_NE, div_result, x);

		// overflow = y_nonzero && mismatch
		// Use: overflow = select(y_nonzero, mismatch, false)
		fbValue false_val = fb_emit_iconst(b, t_bool, 0);
		fbValue overflow = fb_emit_select(b, y_nonzero, mismatch, false_val, t_bool);

		fbAddr res = fb_add_local(b, main_type, nullptr, false);
		i64 off0 = type_offset_of(main_type, 0);
		i64 off1 = type_offset_of(main_type, 1);

		fbValue ptr0 = res.base;
		if (off0 != 0) ptr0 = fb_emit_member(b, res.base, off0);
		fb_emit_store(b, ptr0, result);

		fbValue ptr1 = fb_emit_member(b, res.base, off1);
		fb_emit_store(b, ptr1, overflow);

		fbValue ret = res.base;
		ret.type = main_type;
		return ret;
	}

	// ── Math builtins ───────────────────────────────────────────

	case BuiltinProc_sqrt: {
		fbValue x = fb_build_expr(b, ce->args[0]);
		x = fb_emit_conv(b, x, type);
		fbType ft = fb_data_type(type);
		u32 r = fb_inst_emit(b->proc, FB_SQRT, ft, x.id, FB_NOREG, FB_NOREG, 0, 0);
		return fb_make_value(r, type);
	}

	case BuiltinProc_fused_mul_add: {
		// At -O0: emit FMUL + FADD (no FMA instruction)
		fbValue x = fb_build_expr(b, ce->args[0]);
		fbValue y = fb_build_expr(b, ce->args[1]);
		fbValue z = fb_build_expr(b, ce->args[2]);
		x = fb_emit_conv(b, x, type);
		y = fb_emit_conv(b, y, type);
		z = fb_emit_conv(b, z, type);
		fbValue mul = fb_emit_arith(b, FB_FMUL, x, y, type);
		return fb_emit_arith(b, FB_FADD, mul, z, type);
	}

	// ── Bit manipulation (additional) ───────────────────────────

	case BuiltinProc_reverse_bits: {
		// Bit-reversal via parallel swap: swap adjacent bits, then pairs,
		// nibbles, bytes, and finally byte-swap for 16/32/64-bit types.
		fbValue x = fb_build_expr(b, ce->args[0]);
		Type *t = tv.type;
		x = fb_emit_conv(b, x, t);
		fbType ft = fb_data_type(t);
		i32 bits = fb_type_size(ft) * 8;

		// Swap adjacent bits: x = ((x >> 1) & 0x5555...) | ((x & 0x5555...) << 1)
		i64 m1 = 0;
		for (i32 i = 0; i < bits; i += 2) m1 |= (cast(i64)1 << i);
		fbValue mask1 = fb_emit_iconst(b, t, m1);
		fbValue one = fb_emit_iconst(b, t, 1);
		fbValue sr1 = fb_emit_arith(b, FB_LSHR, x, one, t);
		fbValue a1 = fb_emit_arith(b, FB_AND, sr1, mask1, t);
		fbValue a2 = fb_emit_arith(b, FB_AND, x, mask1, t);
		fbValue sl1 = fb_emit_arith(b, FB_SHL, a2, one, t);
		x = fb_emit_arith(b, FB_OR, a1, sl1, t);

		// Swap adjacent pairs: x = ((x >> 2) & 0x3333...) | ((x & 0x3333...) << 2)
		i64 m2 = 0;
		for (i32 i = 0; i < bits; i += 4) m2 |= (cast(i64)3 << i);
		fbValue mask2 = fb_emit_iconst(b, t, m2);
		fbValue two = fb_emit_iconst(b, t, 2);
		fbValue sr2 = fb_emit_arith(b, FB_LSHR, x, two, t);
		fbValue b1 = fb_emit_arith(b, FB_AND, sr2, mask2, t);
		fbValue b2 = fb_emit_arith(b, FB_AND, x, mask2, t);
		fbValue sl2 = fb_emit_arith(b, FB_SHL, b2, two, t);
		x = fb_emit_arith(b, FB_OR, b1, sl2, t);

		// Swap nibbles: x = ((x >> 4) & 0x0F0F...) | ((x & 0x0F0F...) << 4)
		i64 m3 = 0;
		for (i32 i = 0; i < bits; i += 8) m3 |= (cast(i64)0x0F << i);
		fbValue mask3 = fb_emit_iconst(b, t, m3);
		fbValue four = fb_emit_iconst(b, t, 4);
		fbValue sr3 = fb_emit_arith(b, FB_LSHR, x, four, t);
		fbValue c1 = fb_emit_arith(b, FB_AND, sr3, mask3, t);
		fbValue c2 = fb_emit_arith(b, FB_AND, x, mask3, t);
		fbValue sl3 = fb_emit_arith(b, FB_SHL, c2, four, t);
		x = fb_emit_arith(b, FB_OR, c1, sl3, t);

		// For multi-byte types, byte-swap completes the reversal
		if (bits > 8) {
			u32 r = fb_inst_emit(b->proc, FB_BSWAP, ft, x.id, FB_NOREG, FB_NOREG, 0, 0);
			x = fb_make_value(r, t);
		}
		return x;
	}

	// ── Type introspection ──────────────────────────────────────

	case BuiltinProc_type_info_of: {
		if (build_context.no_rtti) {
			return fb_emit_iconst(b, t_rawptr, 0);
		}
		Ast *arg = ce->args[0];
		Type *t = type_of_expr(arg);
		t = default_type(t);
		isize index = fb_type_info_index(b->module->info, t, false);
		if (index < 0) {
			return fb_emit_iconst(b, t_rawptr, 0);
		}
		// Load from the type_info pointer table: ti_ptrs[index]
		// Find the __$fb_ti_ptrs global
		// We use a SYMADDR + LOAD approach: emit address of ti_ptrs + index*8, load
		// However, at IR build time we don't have the global symbol index.
		// Instead, use a global variable lookup approach.
		// The simplest approach: compute address of type_table.data[index]
		// type_table is a runtime global whose data field points to ti_ptrs
		Entity *tt_entity = scope_lookup_current(b->module->info->runtime_package->scope, str_lit("type_table"));
		if (tt_entity == nullptr) {
			return fb_emit_iconst(b, t_rawptr, 0);
		}
		u32 *gidx = map_get(&b->module->global_entity_map, tt_entity);
		if (gidx == nullptr) {
			return fb_emit_iconst(b, t_rawptr, 0);
		}
		// Load type_table.data (the pointer to the array of ^Type_Info)
		fbValue tt_addr = fb_emit_symaddr(b, FB_GLOBAL_SYM_BASE + *gidx);
		tt_addr.type = t_rawptr;
		fbValue data_ptr = fb_emit_load(b, tt_addr, t_rawptr);
		// Index into the pointer array
		i64 ptr_size = build_context.ptr_size;
		fbValue elem_ptr = fb_emit_array_access(b, data_ptr, fb_emit_iconst(b, t_int, index), ptr_size);
		// Load the ^Type_Info pointer
		return fb_emit_load(b, elem_ptr, t_rawptr);
	}

	case BuiltinProc_typeid_of: {
		Ast *arg = ce->args[0];
		TypeAndValue tav = type_and_value_of_expr(arg);
		GB_ASSERT(tav.mode == Addressing_Type);
		Type *t = default_type(type_of_expr(arg));
		u64 hash = type_hash_canonical_type(t);
		return fb_emit_iconst(b, t_typeid, cast(i64)hash);
	}

	// ── Memory operations (additional) ──────────────────────────

	case BuiltinProc_mem_zero_volatile: {
		// Same as mem_zero at -O0 (volatile semantics not observable without optimization)
		fbValue dst = fb_build_expr(b, ce->args[0]);
		fbValue len = fb_build_expr(b, ce->args[1]);
		len = fb_emit_conv(b, len, t_int);
		fb_emit_memzero_v(b, dst, len, 1);
		return fb_value_nil();
	}

	// ── Pointer arithmetic ───────────────────────────────────────

	case BuiltinProc_ptr_offset: {
		fbValue ptr = fb_build_expr(b, ce->args[0]);
		fbValue offset = fb_build_expr(b, ce->args[1]);
		offset = fb_emit_conv(b, offset, t_int);

		Type *ptr_type = type_of_expr(ce->args[0]);
		Type *elem = type_deref(ptr_type);
		i64 stride = type_size_of(elem);

		return fb_emit_array_access(b, ptr, offset, stride);
	}

	case BuiltinProc_ptr_sub: {
		Type *elem = type_deref(type_of_expr(ce->args[0]));
		i64 elem_size = type_size_of(elem);

		fbValue ptr0 = fb_build_expr(b, ce->args[0]);
		fbValue ptr1 = fb_build_expr(b, ce->args[1]);

		// Convert pointers to integers, subtract, divide by element size
		fbValue i0 = fb_emit(b, FB_PTR2INT, FB_I64, ptr0.id, FB_NOREG, FB_NOREG, 0);
		i0.type = t_int;
		fbValue i1 = fb_emit(b, FB_PTR2INT, FB_I64, ptr1.id, FB_NOREG, FB_NOREG, 0);
		i1.type = t_int;

		fbValue diff = fb_emit_arith(b, FB_SUB, i0, i1, t_int);

		if (elem_size != 1) {
			fbValue stride = fb_emit_iconst(b, t_int, elem_size);
			return fb_emit_arith(b, FB_SDIV, diff, stride, t_int);
		}
		return diff;
	}

	// ── Memory operations ────────────────────────────────────────

	case BuiltinProc_mem_copy: {
		fbValue dst = fb_build_expr(b, ce->args[0]);
		fbValue src = fb_build_expr(b, ce->args[1]);
		fbValue len = fb_build_expr(b, ce->args[2]);
		len = fb_emit_conv(b, len, t_int);
		fb_emit_memcpy(b, dst, src, len, 1);
		return fb_value_nil();
	}

	case BuiltinProc_mem_zero: {
		fbValue dst = fb_build_expr(b, ce->args[0]);
		fbValue len = fb_build_expr(b, ce->args[1]);
		len = fb_emit_conv(b, len, t_int);
		fb_emit_memzero_v(b, dst, len, 1);
		return fb_value_nil();
	}

	case BuiltinProc_mem_copy_non_overlapping: {
		fbValue dst = fb_build_expr(b, ce->args[0]);
		fbValue src = fb_build_expr(b, ce->args[1]);
		fbValue len = fb_build_expr(b, ce->args[2]);
		len = fb_emit_conv(b, len, t_int);
		fb_emit_memcpy(b, dst, src, len, 1);
		return fb_value_nil();
	}

	// ── Control flow / traps ─────────────────────────────────────

	case BuiltinProc_trap:
		fb_inst_emit(b->proc, FB_TRAP, FB_VOID, FB_NOREG, FB_NOREG, FB_NOREG, 0, 0);
		return fb_value_nil();

	case BuiltinProc_debug_trap:
		fb_inst_emit(b->proc, FB_DEBUGBREAK, FB_VOID, FB_NOREG, FB_NOREG, FB_NOREG, 0, 0);
		return fb_value_nil();

	case BuiltinProc_unreachable:
		fb_inst_emit(b->proc, FB_UNREACHABLE, FB_VOID, FB_NOREG, FB_NOREG, FB_NOREG, 0, 0);
		return fb_value_nil();

	// ── Optimization hints ───────────────────────────────────────

	case BuiltinProc_expect: {
		// At -O0, expect is a no-op passthrough — just return the value.
		return fb_build_expr(b, ce->args[0]);
	}

	// ── Volatile memory ──────────────────────────────────────────

	case BuiltinProc_volatile_load: {
		fbValue ptr = fb_build_expr(b, ce->args[0]);
		Type *elem = type_deref(type_of_expr(ce->args[0]));
		// TODO: set volatile flag on the LOAD instruction
		return fb_emit_load(b, ptr, elem);
	}

	case BuiltinProc_volatile_store: {
		fbValue ptr = fb_build_expr(b, ce->args[0]);
		fbValue val = fb_build_expr(b, ce->args[1]);
		// TODO: set volatile flag on the STORE instruction
		fb_emit_store(b, ptr, val);
		return fb_value_nil();
	}

	// ── Unaligned memory access ─────────────────────────────────
	// On x86-64, all scalar loads/stores are naturally unaligned-safe.
	// Aggregates go through memcpy (no alignment requirement).

	case BuiltinProc_unaligned_load: {
		fbValue ptr = fb_build_expr(b, ce->args[0]);
		Type *elem = type_deref(type_of_expr(ce->args[0]));
		if (fb_data_type(elem).kind == FBT_VOID) {
			// Aggregate: copy to properly-aligned temp local
			fbAddr temp = fb_add_local(b, elem, nullptr, false);
			i64 sz = type_size_of(elem);
			fb_emit_memcpy(b, temp.base, ptr, fb_emit_iconst(b, t_int, sz), 1);
			fbValue result = temp.base;
			result.type = elem;
			return result;
		}
		return fb_emit_load(b, ptr, elem);
	}

	case BuiltinProc_unaligned_store: {
		fbValue ptr = fb_build_expr(b, ce->args[0]);
		fbValue val = fb_build_expr(b, ce->args[1]);
		Type *elem = type_deref(type_of_expr(ce->args[0]));
		fb_emit_copy_value(b, ptr, val, elem);
		return fb_value_nil();
	}

	// ── Bit manipulation ─────────────────────────────────────────

	case BuiltinProc_byte_swap: {
		fbValue x = fb_build_expr(b, ce->args[0]);
		fbType ft = fb_data_type(x.type ? x.type : type);
		u32 r = fb_inst_emit(b->proc, FB_BSWAP, ft, x.id, FB_NOREG, FB_NOREG, 0, 0);
		fbValue v = {};
		v.id = r;
		v.type = type;
		return v;
	}

	case BuiltinProc_count_ones: {
		fbValue x = fb_build_expr(b, ce->args[0]);
		fbType ft = fb_data_type(x.type ? x.type : type);
		u32 r = fb_inst_emit(b->proc, FB_POPCNT, ft, x.id, FB_NOREG, FB_NOREG, 0, 0);
		fbValue v = {};
		v.id = r;
		v.type = type;
		return v;
	}

	case BuiltinProc_count_zeros: {
		// count_zeros(x) = bit_width - count_ones(x)
		fbValue x = fb_build_expr(b, ce->args[0]);
		fbType ft = fb_data_type(x.type ? x.type : type);
		i32 bits = fb_type_size(ft) * 8;

		u32 pop_r = fb_inst_emit(b->proc, FB_POPCNT, ft, x.id, FB_NOREG, FB_NOREG, 0, 0);
		fbValue pop = {};
		pop.id = pop_r;
		pop.type = type;

		fbValue width = fb_emit_iconst(b, type, bits);
		return fb_emit_arith(b, FB_SUB, width, pop, type);
	}

	case BuiltinProc_count_leading_zeros: {
		fbValue x = fb_build_expr(b, ce->args[0]);
		fbType ft = fb_data_type(x.type ? x.type : type);
		u32 r = fb_inst_emit(b->proc, FB_CLZ, ft, x.id, FB_NOREG, FB_NOREG, 0, 0);
		fbValue v = {};
		v.id = r;
		v.type = type;
		return v;
	}

	case BuiltinProc_count_trailing_zeros: {
		fbValue x = fb_build_expr(b, ce->args[0]);
		fbType ft = fb_data_type(x.type ? x.type : type);
		u32 r = fb_inst_emit(b->proc, FB_CTZ, ft, x.id, FB_NOREG, FB_NOREG, 0, 0);
		fbValue v = {};
		v.id = r;
		v.type = type;
		return v;
	}

	case BuiltinProc_read_cycle_counter: {
		u32 r = fb_inst_emit(b->proc, FB_CYCLE, FB_I64, FB_NOREG, FB_NOREG, FB_NOREG, 0, 0);
		fbValue v = {};
		v.id = r;
		v.type = t_u64;
		return v;
	}

	case BuiltinProc_cpu_relax: {
		// x86 PAUSE instruction — emitted as a NOP-like hint.
		// We use PREFETCH with level 0 as a proxy (the lowerer can
		// special-case this, or we add a dedicated PAUSE opcode later).
		// For now, emit nothing — cpu_relax is a performance hint.
		return fb_value_nil();
	}

	// ── Size/align/offset (fallback for non-constant cases) ──────

	case BuiltinProc_size_of:
		return fb_emit_iconst(b, t_int, type_size_of(tv.type));

	case BuiltinProc_align_of:
		return fb_emit_iconst(b, t_int, type_align_of(tv.type));

	case BuiltinProc___entry_point: {
		// Call the user's entry point procedure (package main :: main)
		if (b->module->info->entry_point) {
			u32 *proc_idx_ptr = map_get(&fb_entity_proc_map, b->module->info->entry_point);
			if (proc_idx_ptr != nullptr) {
				u32 proc_idx = *proc_idx_ptr;
				fbValue target = fb_emit_symaddr(b, proc_idx);

				// Entry point is Odin CC: pass context as the only arg
				u32 aux_start = b->proc->aux_count;
				u32 arg_count = 0;
				if (b->context_stack.count > 0) {
					fbContextData *ctx = &b->context_stack[b->context_stack.count - 1];
					fbValue ctx_ptr = fb_addr_load(b, ctx->ctx);
					fb_aux_push(b->proc, ctx_ptr.id);
					arg_count = 1;
				}
				u32 r = fb_inst_emit(b->proc, FB_CALL, FB_VOID, target.id, aux_start, arg_count, 0, 0);
				// Mark as Odin CC
				fbInst *call_inst = &b->proc->insts[b->proc->inst_count - 1];
				call_inst->flags = FBCC_ODIN;
			}
		}
		return fb_value_nil();
	}

	// ── Syscall (Linux x86-64) ───────────────────────────────────

	case BuiltinProc_syscall: {
		// Evaluate all args to uintptr, push into aux pool.
		// Two-phase (evaluate then push) to avoid nested-call aux interleaving.
		auto arg_vals = array_make<fbValue>(heap_allocator(), 0, ce->args.count);
		for_array(i, ce->args) {
			fbValue arg = fb_build_expr(b, ce->args[i]);
			arg = fb_emit_conv(b, arg, t_uintptr);
			array_add(&arg_vals, arg);
		}
		u32 aux_start = b->proc->aux_count;
		for_array(i, arg_vals) {
			fb_aux_push(b->proc, arg_vals[i].id);
		}
		array_free(&arg_vals);
		u32 arg_count = b->proc->aux_count - aux_start;

		// FB_ASM with imm=1 signals "syscall" to the lowerer.
		// Encoding: a=aux_start, b=arg_count (mirrors FB_CALL layout).
		fbType ret_type = {FBT_I64, 0};
		u32 r = fb_inst_emit(b->proc, FB_ASM, ret_type, aux_start, arg_count, 0, b->current_loc, 1);
		fbValue result;
		result.id = r;
		result.type = t_uintptr;
		return result;
	}

	// ── Complex/Quaternion component access ─────────────────────

	case BuiltinProc_real: {
		fbValue val = fb_build_expr(b, ce->args[0]);
		Type *val_type = type_of_expr(ce->args[0]);
		Type *ft = base_complex_elem_type(val_type);
		i64 elem_size = type_size_of(ft);

		// val is an aggregate pointer for complex/quaternion
		fbValue ptr;
		if (is_type_complex(val_type)) {
			// Complex layout: {real, imag} — real at offset 0
			ptr = val;
		} else {
			// @QuaternionLayout: {i, j, k, w} — real (w) at index 3
			ptr = fb_emit_member(b, val, elem_size * 3);
		}
		fbValue result = fb_emit_load(b, ptr, ft);
		return fb_emit_conv(b, result, type);
	}

	case BuiltinProc_imag: {
		fbValue val = fb_build_expr(b, ce->args[0]);
		Type *val_type = type_of_expr(ce->args[0]);
		Type *ft = base_complex_elem_type(val_type);
		i64 elem_size = type_size_of(ft);

		fbValue ptr;
		if (is_type_complex(val_type)) {
			// Complex layout: {real, imag} — imag at offset elem_size
			ptr = fb_emit_member(b, val, elem_size);
		} else {
			// @QuaternionLayout: {i, j, k, w} — imag (i) at index 0
			ptr = val;
		}
		fbValue result = fb_emit_load(b, ptr, ft);
		return fb_emit_conv(b, result, type);
	}

	case BuiltinProc_jmag: {
		fbValue val = fb_build_expr(b, ce->args[0]);
		Type *val_type = type_of_expr(ce->args[0]);
		Type *ft = base_complex_elem_type(val_type);
		i64 elem_size = type_size_of(ft);
		// @QuaternionLayout: {i, j, k, w} — j at index 1
		fbValue ptr = fb_emit_member(b, val, elem_size * 1);
		fbValue result = fb_emit_load(b, ptr, ft);
		return fb_emit_conv(b, result, type);
	}

	case BuiltinProc_kmag: {
		fbValue val = fb_build_expr(b, ce->args[0]);
		Type *val_type = type_of_expr(ce->args[0]);
		Type *ft = base_complex_elem_type(val_type);
		i64 elem_size = type_size_of(ft);
		// @QuaternionLayout: {i, j, k, w} — k at index 2
		fbValue ptr = fb_emit_member(b, val, elem_size * 2);
		fbValue result = fb_emit_load(b, ptr, ft);
		return fb_emit_conv(b, result, type);
	}

	case BuiltinProc_conj: {
		fbValue val = fb_build_expr(b, ce->args[0]);
		Type *val_type = type_of_expr(ce->args[0]);
		Type *ft = base_complex_elem_type(val_type);
		i64 elem_size = type_size_of(ft);

		// Conjugate: negate the imaginary components
		fbAddr result = fb_add_local(b, val_type, nullptr, false);
		fb_emit_copy_value(b, result.base, val, val_type);

		if (is_type_complex(val_type)) {
			// Negate imag at offset elem_size
			fbValue imag_ptr = fb_emit_member(b, result.base, elem_size);
			fbValue imag = fb_emit_load(b, imag_ptr, ft);
			fbValue neg = fb_emit_arith(b, FB_FNEG, imag, imag, ft);
			fb_emit_store(b, imag_ptr, neg);
		} else {
			// @QuaternionLayout: negate i(0), j(1), k(2)
			for (i64 i = 0; i < 3; i++) {
				fbValue comp_ptr = fb_emit_member(b, result.base, elem_size * i);
				fbValue comp = fb_emit_load(b, comp_ptr, ft);
				fbValue neg = fb_emit_arith(b, FB_FNEG, comp, comp, ft);
				fb_emit_store(b, comp_ptr, neg);
			}
		}

		result.base.type = val_type;
		return result.base;
	}

	case BuiltinProc_swizzle: {
		isize index_count = ce->args.count - 1;

		if (is_type_simd_vector(tv.type)) {
			fbValue vec = fb_build_expr(b, ce->args[0]);
			if (index_count == 0) {
				return vec;
			}
			// Build mask from compile-time indices
			u32 *mask = gb_alloc_array(permanent_allocator(), u32, index_count);
			for (isize i = 0; i < index_count; i++) {
				TypeAndValue itv = type_and_value_of_expr(ce->args[i + 1]);
				GB_ASSERT(itv.value.kind == ExactValue_Integer);
				mask[i] = cast(u32)big_int_to_i64(&itv.value.value_integer);
			}
			// Store mask in aux array
			u32 aux_base = b->proc->aux_count;
			for (isize i = 0; i < index_count; i++) {
				fb_aux_push(b->proc, mask[i]);
			}
			fbType result_ft = fb_data_type(tv.type);
			u32 r = fb_inst_emit(b->proc, FB_VSHUFFLE, result_ft,
				vec.id, FB_NOREG, FB_NOREG,
				0, cast(i64)aux_base | (cast(i64)index_count << 32));
			return fb_make_value(r, tv.type);
		}

		// Array swizzle: build addr-based gather
		fbAddr src_addr = fb_build_addr(b, ce->args[0]);
		Type *src_type = base_type(type_of_expr(ce->args[0]));
		GB_ASSERT(src_type->kind == Type_Array);
		i64 count = src_type->Array.count;

		if (count <= 4 && index_count <= 4) {
			u8 indices[4] = {};
			u8 idx_count = 0;
			for (isize i = 0; i < index_count; i++) {
				TypeAndValue itv = type_and_value_of_expr(ce->args[i + 1]);
				GB_ASSERT(itv.value.kind == ExactValue_Integer);
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
			return fb_addr_load(b, addr);
		}

		auto indices = slice_make<i32>(permanent_allocator(), index_count);
		for (isize i = 0; i < index_count; i++) {
			TypeAndValue itv = type_and_value_of_expr(ce->args[i + 1]);
			GB_ASSERT(itv.value.kind == ExactValue_Integer);
			indices[i] = cast(i32)big_int_to_i64(&itv.value.value_integer);
		}
		fbAddr addr = {};
		addr.kind = fbAddr_SwizzleLarge;
		addr.base = src_addr.base;
		addr.type = tv.type;
		addr.swizzle_large.indices = indices;
		return fb_addr_load(b, addr);
	}

	default:
		break;
	}

	GB_PANIC("fast backend: unhandled builtin '%.*s' (id=%d)",
		LIT(builtin_procs[id].name), id);
	return fb_value_nil();
}
