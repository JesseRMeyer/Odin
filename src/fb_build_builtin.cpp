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

// Load a field from an aggregate in memory.
// base_ptr points to the start of the aggregate; field is at byte_offset.
gb_internal fbValue fb_load_field(fbBuilder *b, fbValue base_ptr, i64 byte_offset, Type *field_type) {
	fbValue ptr = base_ptr;
	if (byte_offset != 0) {
		ptr = fb_emit_member(b, base_ptr, byte_offset);
	}
	return fb_emit_load(b, ptr, field_type);
}

gb_internal fbValue fb_builtin_len(fbBuilder *b, Ast *arg_expr) {
	Type *t = base_type(type_of_expr(arg_expr));

	// Pointer to container: dereference first, then access fields
	if (is_type_pointer(t)) {
		fbValue ptr = fb_build_expr(b, arg_expr);
		t = base_type(type_deref(type_of_expr(arg_expr)));
		i64 len_offset = build_context.int_size; // field 1 for all container types
		return fb_load_field(b, ptr, len_offset, t_int);
	}

	switch (t->kind) {
	case Type_Array:
		return fb_emit_iconst(b, t_int, t->Array.count);
	case Type_EnumeratedArray:
		return fb_emit_iconst(b, t_int, t->EnumeratedArray.count);
	case Type_Slice:
	case Type_DynamicArray: {
		// Slice:   {data: rawptr, len: int}            → len at int_size
		// DynArr:  {data: rawptr, len: int, cap: int, alloc: Allocator} → len at int_size
		fbAddr addr = fb_build_addr(b, arg_expr);
		return fb_load_field(b, addr.base, build_context.int_size, t_int);
	}
	case Type_Basic:
		if (is_type_string(t)) {
			// string: {data: [^]u8, len: int} → len at int_size
			fbAddr addr = fb_build_addr(b, arg_expr);
			return fb_load_field(b, addr.base, build_context.int_size, t_int);
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
			return fb_load_field(b, ptr, 2 * build_context.int_size, t_int);
		}
		// Slice and string cap == len
		return fb_load_field(b, ptr, build_context.int_size, t_int);
	}

	switch (t->kind) {
	case Type_Array:
		return fb_emit_iconst(b, t_int, t->Array.count);
	case Type_EnumeratedArray:
		return fb_emit_iconst(b, t_int, t->EnumeratedArray.count);
	case Type_Slice: {
		// Slice has no separate cap; cap(slice) == len(slice) in Odin
		fbAddr addr = fb_build_addr(b, arg_expr);
		return fb_load_field(b, addr.base, build_context.int_size, t_int);
	}
	case Type_DynamicArray: {
		// DynArr: cap is field 2 at 2*int_size
		fbAddr addr = fb_build_addr(b, arg_expr);
		return fb_load_field(b, addr.base, 2 * build_context.int_size, t_int);
	}
	case Type_Basic:
		if (is_type_string(t)) {
			// cap(string) == len(string)
			fbAddr addr = fb_build_addr(b, arg_expr);
			return fb_load_field(b, addr.base, build_context.int_size, t_int);
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
// Main dispatch
// ───────────────────────────────────────────────────────────────────────

gb_internal fbValue fb_build_builtin_proc(fbBuilder *b, Ast *expr, TypeAndValue const &tv, BuiltinProcId id) {
	ast_node(ce, CallExpr, expr);
	Type *type = type_of_expr(expr);

	// SIMD builtins: deferred to Phase 8
	if (BuiltinProc__simd_begin < id && id < BuiltinProc__simd_end) {
		GB_PANIC("fast backend: SIMD builtins not yet supported");
	}

	// Atomic builtins: deferred to Phase 8
	if (BuiltinProc__atomic_begin < id && id < BuiltinProc__atomic_end) {
		GB_PANIC("fast backend: atomic builtins not yet supported");
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

	default:
		break;
	}

	GB_PANIC("fast backend: unhandled builtin '%.*s' (id=%d)",
		LIT(builtin_procs[id].name), id);
	return fb_value_nil();
}
