// fb_type_info.cpp — Runtime Type Info (RTTI) generation for the fast backend.
// Generates the type_table, type_info entries, and member buffers as globals
// in the .data section with appropriate data relocations.

// ───────────────────────────────────────────────────────────────────────
// Type info index lookup (mirrors lb_type_info_index / cg_type_info_index)
// ───────────────────────────────────────────────────────────────────────

gb_internal isize fb_type_info_index(CheckerInfo *info, Type *type, bool err_on_not_found) {
	type = default_type(type);
	if (type == t_llvm_bool) {
		type = t_bool;
	}
	u64 hash = type_hash_canonical_type(type);
	return type_info_index(info, {type, hash}, err_on_not_found);
}

// ───────────────────────────────────────────────────────────────────────
// Typeid encoding (same as cg_typeid_as_u64)
// ───────────────────────────────────────────────────────────────────────

gb_internal u64 fb_typeid_as_u64(CheckerInfo *info, Type *type) {
	type = default_type(type);
	// typeid is the raw canonical hash — same as what typeid_of produces at compile time
	return type_hash_canonical_type(type);
}

// ───────────────────────────────────────────────────────────────────────
// Helper: write integer/pointer values into raw byte buffers
// ───────────────────────────────────────────────────────────────────────

gb_internal void fb_ti_write_int(u8 *buf, i64 offset, i64 value, i64 size) {
	switch (size) {
	case 1: *cast(u8  *)(buf + offset) = cast(u8)value;  break;
	case 2: *cast(u16 *)(buf + offset) = cast(u16)value; break;
	case 4: *cast(u32 *)(buf + offset) = cast(u32)value; break;
	case 8: *cast(u64 *)(buf + offset) = cast(u64)value; break;
	}
}

gb_internal void fb_ti_write_uint(u8 *buf, i64 offset, u64 value, i64 size) {
	switch (size) {
	case 1: *cast(u8  *)(buf + offset) = cast(u8)value;  break;
	case 2: *cast(u16 *)(buf + offset) = cast(u16)value; break;
	case 4: *cast(u32 *)(buf + offset) = cast(u32)value; break;
	case 8: *cast(u64 *)(buf + offset) = cast(u64)value; break;
	}
}

// Write a string {data_ptr, len} into buf at `buf_offset`.
// `reloc_offset` is the absolute offset within the global for the data reloc.
gb_internal void fb_ti_write_string(fbModule *m, u32 global_idx, u8 *buf, i64 buf_offset, i64 reloc_offset, String str) {
	i64 ptr_size = build_context.ptr_size;
	// len
	fb_ti_write_int(buf, buf_offset + ptr_size, str.len, ptr_size);
	// data pointer: intern in rodata, record reloc
	if (str.len > 0) {
		u32 rodata_sym = fb_module_intern_string_data(m, str);
		fbDataReloc dr = {};
		dr.global_idx    = global_idx;
		dr.local_offset  = cast(u32)reloc_offset;
		dr.target_sym    = rodata_sym;
		dr.addend        = 0;
		array_add(&m->data_relocs, dr);
	}
}

// Write a ^Type_Info pointer into buf at `buf_offset`.
// `reloc_offset` is the absolute offset within the global for the data reloc.
gb_internal void fb_ti_write_type_info_ptr(fbModule *m, u32 global_idx, u8 *buf, i64 buf_offset, i64 reloc_offset,
                                           u32 ti_data_global_idx, Type *type, i64 type_info_size) {
	if (type == nullptr) return;
	isize index = fb_type_info_index(m->info, type, false);
	if (index < 0) return;

	fbDataReloc dr = {};
	dr.global_idx   = global_idx;
	dr.local_offset = cast(u32)reloc_offset;
	dr.target_sym   = FB_GLOBAL_SYM_BASE + ti_data_global_idx;
	dr.addend       = index * type_info_size;
	array_add(&m->data_relocs, dr);
}

// ───────────────────────────────────────────────────────────────────────
// Main entry point
// ───────────────────────────────────────────────────────────────────────

gb_internal void fb_generate_type_info(fbModule *m) {
	if (build_context.no_rtti) {
		return;
	}

	CheckerInfo *info = m->info;
	i64 ptr_size = build_context.ptr_size;
	i64 int_size = build_context.int_size;

	// ── Compute layout constants ────────────────────────────────────
	i64 type_info_size = type_size_of(t_type_info);
	i64 size_offset    = type_offset_of(t_type_info, 0);
	i64 align_offset   = type_offset_of(t_type_info, 1);
	i64 flags_offset   = type_offset_of(t_type_info, 2);
	i64 id_offset      = type_offset_of(t_type_info, 3);
	i64 variant_offset = type_offset_of(t_type_info, 4);

	Type *type_info_union = base_type(t_type_info)->Struct.fields[4]->type;
	GB_ASSERT(type_info_union->kind == Type_Union);

	i64 union_tag_offset_within_union = type_info_union->Union.variant_block_size;
	Type *ti_union_tag_type = union_tag_type(type_info_union);
	i64 ti_union_tag_sz = type_size_of(ti_union_tag_type);

	// ── Count types ─────────────────────────────────────────────────
	isize type_count = info->type_info_types_hash_map.count;
	if (type_count <= 0) return;

	// ── Count member buffer entries ─────────────────────────────────
	isize member_count = 0;
	isize offsets_extra = 0;
	for (auto const &tt : info->type_info_types_hash_map) {
		Type *t = tt.type;
		if (t == nullptr) continue;
		isize index = fb_type_info_index(info, t, false);
		if (index < 0) continue;

		switch (t->kind) {
		case Type_Union:    member_count += t->Union.variants.count; break;
		case Type_Struct:   member_count += t->Struct.fields.count;  break;
		case Type_Tuple:    member_count += t->Tuple.variables.count; break;
		case Type_BitField:
			member_count += t->BitField.fields.count;
			offsets_extra += t->BitField.fields.count;
			break;
		default: break;
		}
	}

	// ── Allocate globals ────────────────────────────────────────────
	// 1. ti_data: contiguous array of type_count Type_Info structs
	i64 ti_data_size = type_count * type_info_size;
	u8 *ti_data_buf = gb_alloc_array(heap_allocator(), u8, ti_data_size);
	gb_zero_size(ti_data_buf, ti_data_size);

	fbGlobalEntry ti_data_entry = {};
	ti_data_entry.name      = str_lit("__$fb_ti_data");
	ti_data_entry.odin_type = t_type_info;
	ti_data_entry.init_data = ti_data_buf;
	ti_data_entry.size      = cast(u32)ti_data_size;
	ti_data_entry.align     = cast(u32)type_align_of(t_type_info);
	ti_data_entry.is_export = false;
	ti_data_entry.is_foreign = false;
	u32 ti_data_gidx = cast(u32)m->global_entries.count;
	array_add(&m->global_entries, ti_data_entry);

	// 2. ti_ptrs: array of type_count pointers (^Type_Info)
	i64 ti_ptrs_size = type_count * ptr_size;
	u8 *ti_ptrs_buf = gb_alloc_array(heap_allocator(), u8, ti_ptrs_size);
	gb_zero_size(ti_ptrs_buf, ti_ptrs_size);

	fbGlobalEntry ti_ptrs_entry = {};
	ti_ptrs_entry.name      = str_lit("__$fb_ti_ptrs");
	ti_ptrs_entry.odin_type = t_type_info_ptr;
	ti_ptrs_entry.init_data = ti_ptrs_buf;
	ti_ptrs_entry.size      = cast(u32)ti_ptrs_size;
	ti_ptrs_entry.align     = cast(u32)ptr_size;
	u32 ti_ptrs_gidx = cast(u32)m->global_entries.count;
	array_add(&m->global_entries, ti_ptrs_entry);

	// 3. Member buffers (types, names, offsets, usings, tags)
	i64 member_types_size   = member_count * ptr_size;
	i64 member_names_size   = member_count * (ptr_size + int_size); // string = {ptr, len}
	i64 member_offsets_size = (member_count + offsets_extra) * int_size; // uintptr
	i64 member_usings_size  = member_count * 1; // bool
	i64 member_tags_size    = member_count * (ptr_size + int_size); // string

	u8 *member_types_buf   = member_types_size   > 0 ? gb_alloc_array(heap_allocator(), u8, member_types_size)   : nullptr;
	u8 *member_names_buf   = member_names_size   > 0 ? gb_alloc_array(heap_allocator(), u8, member_names_size)   : nullptr;
	u8 *member_offsets_buf = member_offsets_size > 0 ? gb_alloc_array(heap_allocator(), u8, member_offsets_size) : nullptr;
	u8 *member_usings_buf  = member_usings_size  > 0 ? gb_alloc_array(heap_allocator(), u8, member_usings_size)  : nullptr;
	u8 *member_tags_buf    = member_tags_size    > 0 ? gb_alloc_array(heap_allocator(), u8, member_tags_size)    : nullptr;

	if (member_types_buf)   gb_zero_size(member_types_buf,   member_types_size);
	if (member_names_buf)   gb_zero_size(member_names_buf,   member_names_size);
	if (member_offsets_buf) gb_zero_size(member_offsets_buf, member_offsets_size);
	if (member_usings_buf)  gb_zero_size(member_usings_buf,  member_usings_size);
	if (member_tags_buf)    gb_zero_size(member_tags_buf,    member_tags_size);

	auto add_member_global = [&](String name, u8 *buf, i64 size, i64 align) -> u32 {
		if (buf == nullptr || size == 0) {
			fbGlobalEntry e = {};
			e.name = name;
			e.size = 0;
			e.align = 1;
			u32 idx = cast(u32)m->global_entries.count;
			array_add(&m->global_entries, e);
			return idx;
		}
		fbGlobalEntry e = {};
		e.name      = name;
		e.init_data = buf;
		e.size      = cast(u32)size;
		e.align     = cast(u32)align;
		u32 idx = cast(u32)m->global_entries.count;
		array_add(&m->global_entries, e);
		return idx;
	};

	u32 mb_types_gidx   = add_member_global(str_lit("__$fb_ti_mt"), member_types_buf,   member_types_size,   ptr_size);
	u32 mb_names_gidx   = add_member_global(str_lit("__$fb_ti_mn"), member_names_buf,   member_names_size,   ptr_size);
	u32 mb_offsets_gidx = add_member_global(str_lit("__$fb_ti_mo"), member_offsets_buf, member_offsets_size, int_size);
	u32 mb_usings_gidx  = add_member_global(str_lit("__$fb_ti_mu"), member_usings_buf,  member_usings_size,  1);
	u32 mb_tags_gidx    = add_member_global(str_lit("__$fb_ti_mg"), member_tags_buf,    member_tags_size,    ptr_size);

	// Running indices into member buffers
	isize mb_index = 0;
	isize mb_offset_index = 0; // separate for offsets due to offsets_extra

	// ── Fill pointer table ──────────────────────────────────────────
	// Each pointer = &ti_data[i], i.e., reloc targeting ti_data + i*type_info_size
	for (isize i = 0; i < type_count; i++) {
		fbDataReloc dr = {};
		dr.global_idx   = ti_ptrs_gidx;
		dr.local_offset = cast(u32)(i * ptr_size);
		dr.target_sym   = FB_GLOBAL_SYM_BASE + ti_data_gidx;
		dr.addend       = i * type_info_size;
		array_add(&m->data_relocs, dr);
	}

	// ── Serialize each type ─────────────────────────────────────────
	auto entries_handled = slice_make<bool>(heap_allocator(), type_count);
	defer (gb_free(heap_allocator(), entries_handled.data));
	entries_handled[0] = true;

	for_array(type_info_type_index, info->type_info_types_hash_map) {
		Type *t = info->type_info_types_hash_map[type_info_type_index].type;
		if (t == nullptr || t == t_invalid) continue;

		isize entry_index = fb_type_info_index(info, t, false);
		if (entry_index <= 0) continue;
		if (entries_handled[entry_index]) continue;
		entries_handled[entry_index] = true;

		u8 *entry = ti_data_buf + entry_index * type_info_size;

		// Header fields
		i64 size  = type_size_of(t);
		i64 align = type_align_of(t);
		u32 flags = type_info_flags_of_type(t);
		u64 id    = fb_typeid_as_u64(info, t);

		fb_ti_write_int (entry, size_offset,  size,  int_size);
		fb_ti_write_int (entry, align_offset, align, int_size);
		fb_ti_write_uint(entry, flags_offset, flags, 4);
		fb_ti_write_uint(entry, id_offset,    id,    ptr_size);

		// Variant data starts at variant_offset within the entry
		u8 *var = entry + variant_offset;
		i64 var_base = entry_index * type_info_size + variant_offset;

		Type *tag_type = nullptr;

		switch (t->kind) {
		case Type_Named: {
			tag_type = t_type_info_named;

			// name: string
			i64 name_off = type_offset_of(tag_type, 0);
			String name = t->Named.type_name->token.string;
			fb_ti_write_string(m, ti_data_gidx, entry, variant_offset + name_off, var_base + name_off, name);

			// base: ^Type_Info
			i64 base_off = type_offset_of(tag_type, 1);
			fb_ti_write_type_info_ptr(m, ti_data_gidx, entry, variant_offset + base_off, var_base + base_off,
			                          ti_data_gidx, t->Named.base, type_info_size);

			// pkg: string
			if (t->Named.type_name->pkg) {
				i64 pkg_off = type_offset_of(tag_type, 2);
				fb_ti_write_string(m, ti_data_gidx, entry, variant_offset + pkg_off, var_base + pkg_off,
				                   t->Named.type_name->pkg->name);
			}

			// loc: ^Source_Code_Location — skip for now (would need its own global)
			break;
		}

		case Type_Basic:
			switch (t->Basic.kind) {
			case Basic_bool: case Basic_b8: case Basic_b16: case Basic_b32: case Basic_b64:
				tag_type = t_type_info_boolean;
				break;

			case Basic_i8: case Basic_u8: case Basic_i16: case Basic_u16:
			case Basic_i32: case Basic_u32: case Basic_i64: case Basic_u64:
			case Basic_i128: case Basic_u128:
			case Basic_i16le: case Basic_u16le: case Basic_i32le: case Basic_u32le:
			case Basic_i64le: case Basic_u64le: case Basic_i128le: case Basic_u128le:
			case Basic_i16be: case Basic_u16be: case Basic_i32be: case Basic_u32be:
			case Basic_i64be: case Basic_u64be: case Basic_i128be: case Basic_u128be:
			case Basic_int: case Basic_uint: case Basic_uintptr: {
				tag_type = t_type_info_integer;
				bool is_signed = (t->Basic.flags & BasicFlag_Unsigned) == 0;
				u8 endianness = 0;
				if (t->Basic.flags & BasicFlag_EndianLittle) endianness = 1;
				else if (t->Basic.flags & BasicFlag_EndianBig) endianness = 2;
				var[0] = cast(u8)is_signed;
				var[1] = endianness;
				break;
			}

			case Basic_rune:
				tag_type = t_type_info_rune;
				break;

			case Basic_f16: case Basic_f32: case Basic_f64:
			case Basic_f16le: case Basic_f32le: case Basic_f64le:
			case Basic_f16be: case Basic_f32be: case Basic_f64be: {
				tag_type = t_type_info_float;
				u8 endianness = 0;
				if (t->Basic.flags & BasicFlag_EndianLittle) endianness = 1;
				else if (t->Basic.flags & BasicFlag_EndianBig) endianness = 2;
				var[0] = endianness;
				break;
			}

			case Basic_complex32: case Basic_complex64: case Basic_complex128:
				tag_type = t_type_info_complex;
				break;

			case Basic_quaternion64: case Basic_quaternion128: case Basic_quaternion256:
				tag_type = t_type_info_quaternion;
				break;

			case Basic_rawptr:
				tag_type = t_type_info_pointer;
				break;

			case Basic_string: {
				tag_type = t_type_info_string;
				// is_cstring = false, encoding = UTF_8 (0) — both zero, already set
				break;
			}
			case Basic_cstring: {
				tag_type = t_type_info_string;
				var[0] = 1; // is_cstring = true
				break;
			}

			case Basic_any:
				tag_type = t_type_info_any;
				break;

			case Basic_typeid:
				tag_type = t_type_info_typeid;
				break;

			default: break;
			}
			break;

		case Type_Pointer: {
			tag_type = t_type_info_pointer;
			i64 elem_off = type_offset_of(tag_type, 0);
			fb_ti_write_type_info_ptr(m, ti_data_gidx, entry, variant_offset + elem_off, var_base + elem_off,
			                          ti_data_gidx, t->Pointer.elem, type_info_size);
			break;
		}

		case Type_MultiPointer: {
			tag_type = t_type_info_multi_pointer;
			i64 elem_off = type_offset_of(tag_type, 0);
			fb_ti_write_type_info_ptr(m, ti_data_gidx, entry, variant_offset + elem_off, var_base + elem_off,
			                          ti_data_gidx, t->MultiPointer.elem, type_info_size);
			break;
		}

		case Type_SoaPointer: {
			tag_type = t_type_info_soa_pointer;
			i64 elem_off = type_offset_of(tag_type, 0);
			fb_ti_write_type_info_ptr(m, ti_data_gidx, entry, variant_offset + elem_off, var_base + elem_off,
			                          ti_data_gidx, t->SoaPointer.elem, type_info_size);
			break;
		}

		case Type_Array: {
			tag_type = t_type_info_array;
			i64 elem_off      = type_offset_of(tag_type, 0);
			i64 elem_size_off = type_offset_of(tag_type, 1);
			i64 count_off     = type_offset_of(tag_type, 2);
			fb_ti_write_type_info_ptr(m, ti_data_gidx, entry, variant_offset + elem_off, var_base + elem_off,
			                          ti_data_gidx, t->Array.elem, type_info_size);
			fb_ti_write_int(var, elem_size_off, type_size_of(t->Array.elem), int_size);
			fb_ti_write_int(var, count_off, t->Array.count, int_size);
			break;
		}

		case Type_EnumeratedArray: {
			tag_type = t_type_info_enumerated_array;
			i64 elem_off      = type_offset_of(tag_type, 0);
			i64 index_off     = type_offset_of(tag_type, 1);
			i64 elem_size_off = type_offset_of(tag_type, 2);
			i64 count_off     = type_offset_of(tag_type, 3);
			i64 min_off       = type_offset_of(tag_type, 4);
			i64 max_off       = type_offset_of(tag_type, 5);
			i64 is_sparse_off = type_offset_of(tag_type, 6);

			fb_ti_write_type_info_ptr(m, ti_data_gidx, entry, variant_offset + elem_off, var_base + elem_off,
			                          ti_data_gidx, t->EnumeratedArray.elem, type_info_size);
			fb_ti_write_type_info_ptr(m, ti_data_gidx, entry, variant_offset + index_off, var_base + index_off,
			                          ti_data_gidx, t->EnumeratedArray.index, type_info_size);
			fb_ti_write_int(var, elem_size_off, type_size_of(t->EnumeratedArray.elem), int_size);
			fb_ti_write_int(var, count_off, t->EnumeratedArray.count, int_size);

			if (t->EnumeratedArray.min_value != nullptr) {
				i64 min_val = exact_value_to_i64(*t->EnumeratedArray.min_value);
				i64 max_val = exact_value_to_i64(*t->EnumeratedArray.max_value);
				fb_ti_write_int(var, min_off, min_val, 8); // Type_Info_Enum_Value = i64
				fb_ti_write_int(var, max_off, max_val, 8);
			}
			var[is_sparse_off] = t->EnumeratedArray.is_sparse ? 1 : 0;
			break;
		}

		case Type_DynamicArray: {
			tag_type = t_type_info_dynamic_array;
			i64 elem_off      = type_offset_of(tag_type, 0);
			i64 elem_size_off = type_offset_of(tag_type, 1);
			fb_ti_write_type_info_ptr(m, ti_data_gidx, entry, variant_offset + elem_off, var_base + elem_off,
			                          ti_data_gidx, t->DynamicArray.elem, type_info_size);
			fb_ti_write_int(var, elem_size_off, type_size_of(t->DynamicArray.elem), int_size);
			break;
		}

		case Type_Slice: {
			tag_type = t_type_info_slice;
			i64 elem_off      = type_offset_of(tag_type, 0);
			i64 elem_size_off = type_offset_of(tag_type, 1);
			fb_ti_write_type_info_ptr(m, ti_data_gidx, entry, variant_offset + elem_off, var_base + elem_off,
			                          ti_data_gidx, t->Slice.elem, type_info_size);
			fb_ti_write_int(var, elem_size_off, type_size_of(t->Slice.elem), int_size);
			break;
		}

		case Type_Proc: {
			tag_type = t_type_info_procedure;
			i64 params_off  = type_offset_of(tag_type, 0);
			i64 results_off = type_offset_of(tag_type, 1);
			i64 variadic_off = type_offset_of(tag_type, 2);
			i64 convention_off = type_offset_of(tag_type, 3);

			if (t->Proc.params != nullptr) {
				fb_ti_write_type_info_ptr(m, ti_data_gidx, entry, variant_offset + params_off, var_base + params_off,
				                          ti_data_gidx, t->Proc.params, type_info_size);
			}
			if (t->Proc.results != nullptr) {
				fb_ti_write_type_info_ptr(m, ti_data_gidx, entry, variant_offset + results_off, var_base + results_off,
				                          ti_data_gidx, t->Proc.results, type_info_size);
			}
			var[variadic_off] = t->Proc.variadic ? 1 : 0;
			var[convention_off] = cast(u8)t->Proc.calling_convention;
			break;
		}

		case Type_Tuple: {
			// Type_Info_Parameters: types: []^Type_Info, names: []string
			tag_type = t_type_info_parameters;
			isize count = t->Tuple.variables.count;

			if (count > 0) {
				i64 types_off = type_offset_of(tag_type, 0); // slice: {data, len}
				i64 names_off = type_offset_of(tag_type, 1);

				isize base_idx = mb_index;

				// Write member types
				for (isize i = 0; i < count; i++) {
					i64 elem_off = (base_idx + i) * ptr_size;
					fb_ti_write_type_info_ptr(m, mb_types_gidx, member_types_buf, elem_off, elem_off,
					                          ti_data_gidx, t->Tuple.variables[i]->type, type_info_size);
				}

				// Write member names
				for (isize i = 0; i < count; i++) {
					i64 elem_off = (base_idx + i) * (ptr_size + int_size);
					String name = t->Tuple.variables[i]->token.string;
					fb_ti_write_string(m, mb_names_gidx, member_names_buf, elem_off, elem_off, name);
				}

				// Write slice headers: {data_ptr, len}
				// types slice
				fb_ti_write_int(var, types_off + ptr_size, count, int_size);
				{
					fbDataReloc dr = {};
					dr.global_idx   = ti_data_gidx;
					dr.local_offset = cast(u32)(var_base + types_off);
					dr.target_sym   = FB_GLOBAL_SYM_BASE + mb_types_gidx;
					dr.addend       = base_idx * ptr_size;
					array_add(&m->data_relocs, dr);
				}
				// names slice
				fb_ti_write_int(var, names_off + ptr_size, count, int_size);
				{
					fbDataReloc dr = {};
					dr.global_idx   = ti_data_gidx;
					dr.local_offset = cast(u32)(var_base + names_off);
					dr.target_sym   = FB_GLOBAL_SYM_BASE + mb_names_gidx;
					dr.addend       = base_idx * (ptr_size + int_size);
					array_add(&m->data_relocs, dr);
				}

				mb_index += count;
			}
			break;
		}

		case Type_Enum: {
			tag_type = t_type_info_enum;
			i64 base_off  = type_offset_of(tag_type, 0);
			i64 names_off = type_offset_of(tag_type, 1); // []string
			i64 values_off = type_offset_of(tag_type, 2); // []Type_Info_Enum_Value (i64)

			Type *bt = base_type(t);
			fb_ti_write_type_info_ptr(m, ti_data_gidx, entry, variant_offset + base_off, var_base + base_off,
			                          ti_data_gidx, bt->Enum.base_type, type_info_size);

			isize field_count = bt->Enum.fields.count;
			if (field_count > 0) {
				// Allocate rodata for enum names and values
				i64 names_buf_size  = field_count * (ptr_size + int_size);
				i64 values_buf_size = field_count * 8; // i64 each
				u8 *enum_names  = gb_alloc_array(heap_allocator(), u8, names_buf_size);
				u8 *enum_values = gb_alloc_array(heap_allocator(), u8, values_buf_size);
				gb_zero_size(enum_names,  names_buf_size);
				gb_zero_size(enum_values, values_buf_size);

				// Create globals for enum member data
				fbGlobalEntry en_entry = {};
				en_entry.name = str_lit("__$fb_ti_en");
				en_entry.init_data = enum_names;
				en_entry.size = cast(u32)names_buf_size;
				en_entry.align = cast(u32)ptr_size;
				u32 en_gidx = cast(u32)m->global_entries.count;
				array_add(&m->global_entries, en_entry);

				fbGlobalEntry ev_entry = {};
				ev_entry.name = str_lit("__$fb_ti_ev");
				ev_entry.init_data = enum_values;
				ev_entry.size = cast(u32)values_buf_size;
				ev_entry.align = 8;
				u32 ev_gidx = cast(u32)m->global_entries.count;
				array_add(&m->global_entries, ev_entry);

				for (isize i = 0; i < field_count; i++) {
					Entity *f = bt->Enum.fields[i];
					i64 name_elem_off = i * (ptr_size + int_size);
					fb_ti_write_string(m, en_gidx, enum_names, name_elem_off, name_elem_off, f->token.string);

					i64 val = exact_value_to_i64(f->Constant.value);
					fb_ti_write_int(enum_values, i * 8, val, 8);
				}

				// names slice in variant
				fb_ti_write_int(var, names_off + ptr_size, field_count, int_size);
				{
					fbDataReloc dr = {};
					dr.global_idx   = ti_data_gidx;
					dr.local_offset = cast(u32)(var_base + names_off);
					dr.target_sym   = FB_GLOBAL_SYM_BASE + en_gidx;
					dr.addend       = 0;
					array_add(&m->data_relocs, dr);
				}
				// values slice in variant
				fb_ti_write_int(var, values_off + ptr_size, field_count, int_size);
				{
					fbDataReloc dr = {};
					dr.global_idx   = ti_data_gidx;
					dr.local_offset = cast(u32)(var_base + values_off);
					dr.target_sym   = FB_GLOBAL_SYM_BASE + ev_gidx;
					dr.addend       = 0;
					array_add(&m->data_relocs, dr);
				}
			}
			break;
		}

		case Type_Union: {
			tag_type = t_type_info_union;
			i64 variants_off   = type_offset_of(tag_type, 0); // []^Type_Info
			i64 tag_offset_off = type_offset_of(tag_type, 1); // uintptr
			i64 tag_type_off   = type_offset_of(tag_type, 2); // ^Type_Info
			i64 equal_off      = type_offset_of(tag_type, 3); // Equal_Proc
			i64 custom_align_off = type_offset_of(tag_type, 4);
			i64 no_nil_off     = type_offset_of(tag_type, 5);
			i64 shared_nil_off = type_offset_of(tag_type, 6);

			Type *bt = base_type(t);
			isize variant_count = bt->Union.variants.count;

			if (variant_count > 0) {
				isize base_idx = mb_index;

				for (isize i = 0; i < variant_count; i++) {
					i64 elem_off = (base_idx + i) * ptr_size;
					fb_ti_write_type_info_ptr(m, mb_types_gidx, member_types_buf, elem_off, elem_off,
					                          ti_data_gidx, bt->Union.variants[i], type_info_size);
				}

				// variants slice
				fb_ti_write_int(var, variants_off + ptr_size, variant_count, int_size);
				{
					fbDataReloc dr = {};
					dr.global_idx   = ti_data_gidx;
					dr.local_offset = cast(u32)(var_base + variants_off);
					dr.target_sym   = FB_GLOBAL_SYM_BASE + mb_types_gidx;
					dr.addend       = base_idx * ptr_size;
					array_add(&m->data_relocs, dr);
				}

				mb_index += variant_count;
			}

			i64 tag_sz = union_tag_size(bt);
			if (tag_sz > 0) {
				fb_ti_write_uint(var, tag_offset_off, cast(u64)bt->Union.variant_block_size, int_size);
				fb_ti_write_type_info_ptr(m, ti_data_gidx, entry, variant_offset + tag_type_off, var_base + tag_type_off,
				                          ti_data_gidx, union_tag_type(bt), type_info_size);
			}

			var[custom_align_off] = bt->Union.custom_align != 0 ? 1 : 0;
			var[no_nil_off]       = bt->Union.kind == UnionType_no_nil ? 1 : 0;
			var[shared_nil_off]   = bt->Union.kind == UnionType_shared_nil ? 1 : 0;
			break;
		}

		case Type_Struct: {
			tag_type = t_type_info_struct;
			i64 types_off      = type_offset_of(tag_type, 0); // [^]^Type_Info
			i64 names_off      = type_offset_of(tag_type, 1); // [^]string
			i64 offsets_off    = type_offset_of(tag_type, 2); // [^]uintptr
			i64 usings_off     = type_offset_of(tag_type, 3); // [^]bool
			i64 tags_off       = type_offset_of(tag_type, 4); // [^]string
			i64 field_count_off = type_offset_of(tag_type, 5); // i32
			i64 flags_off_s    = type_offset_of(tag_type, 6); // u8 flags
			i64 soa_kind_off   = type_offset_of(tag_type, 7);
			i64 soa_len_off    = type_offset_of(tag_type, 8);
			i64 soa_base_off   = type_offset_of(tag_type, 9);

			Type *bt = base_type(t);
			isize field_count = bt->Struct.fields.count;

			fb_ti_write_int(var, field_count_off, cast(i64)field_count, 4);

			// Struct flags
			u8 struct_flags = 0;
			if (bt->Struct.is_packed)    struct_flags |= (1 << 0);
			if (bt->Struct.is_raw_union) struct_flags |= (1 << 1);
			if (bt->Struct.custom_align != 0) struct_flags |= (1 << 3);
			if (is_type_comparable(t) && is_type_simple_compare(t)) struct_flags |= (1 << 4);
			var[flags_off_s] = struct_flags;

			if (field_count > 0) {
				isize base_idx = mb_index;

				// Types
				for (isize i = 0; i < field_count; i++) {
					Entity *f = bt->Struct.fields[i];
					i64 elem_off = (base_idx + i) * ptr_size;
					fb_ti_write_type_info_ptr(m, mb_types_gidx, member_types_buf, elem_off, elem_off,
					                          ti_data_gidx, f->type, type_info_size);
				}

				// Names
				for (isize i = 0; i < field_count; i++) {
					Entity *f = bt->Struct.fields[i];
					i64 elem_off = (base_idx + i) * (ptr_size + int_size);
					fb_ti_write_string(m, mb_names_gidx, member_names_buf, elem_off, elem_off, f->token.string);
				}

				// Offsets
				type_set_offsets(t);
				for (isize i = 0; i < field_count; i++) {
					i64 off_val = bt->Struct.offsets[i];
					i64 elem_off = (mb_offset_index + i) * int_size;
					fb_ti_write_uint(member_offsets_buf, elem_off, cast(u64)off_val, int_size);
				}

				// Usings
				for (isize i = 0; i < field_count; i++) {
					Entity *f = bt->Struct.fields[i];
					member_usings_buf[base_idx + i] = (f->flags & EntityFlag_Using) ? 1 : 0;
				}

				// Tags
				for (isize i = 0; i < field_count; i++) {
					i64 elem_off = (base_idx + i) * (ptr_size + int_size);
					String tag = {};
					if (bt->Struct.tags != nullptr) {
						tag = bt->Struct.tags[i];
					}
					fb_ti_write_string(m, mb_tags_gidx, member_tags_buf, elem_off, elem_off, tag);
				}

				// Write multi-pointers: just the data pointer (no length for [^]T)
				{
					fbDataReloc dr = {};
					dr.global_idx   = ti_data_gidx;
					dr.local_offset = cast(u32)(var_base + types_off);
					dr.target_sym   = FB_GLOBAL_SYM_BASE + mb_types_gidx;
					dr.addend       = base_idx * ptr_size;
					array_add(&m->data_relocs, dr);
				}
				{
					fbDataReloc dr = {};
					dr.global_idx   = ti_data_gidx;
					dr.local_offset = cast(u32)(var_base + names_off);
					dr.target_sym   = FB_GLOBAL_SYM_BASE + mb_names_gidx;
					dr.addend       = base_idx * (ptr_size + int_size);
					array_add(&m->data_relocs, dr);
				}
				{
					fbDataReloc dr = {};
					dr.global_idx   = ti_data_gidx;
					dr.local_offset = cast(u32)(var_base + offsets_off);
					dr.target_sym   = FB_GLOBAL_SYM_BASE + mb_offsets_gidx;
					dr.addend       = mb_offset_index * int_size;
					array_add(&m->data_relocs, dr);
				}
				{
					fbDataReloc dr = {};
					dr.global_idx   = ti_data_gidx;
					dr.local_offset = cast(u32)(var_base + usings_off);
					dr.target_sym   = FB_GLOBAL_SYM_BASE + mb_usings_gidx;
					dr.addend       = base_idx;
					array_add(&m->data_relocs, dr);
				}
				{
					fbDataReloc dr = {};
					dr.global_idx   = ti_data_gidx;
					dr.local_offset = cast(u32)(var_base + tags_off);
					dr.target_sym   = FB_GLOBAL_SYM_BASE + mb_tags_gidx;
					dr.addend       = base_idx * (ptr_size + int_size);
					array_add(&m->data_relocs, dr);
				}

				mb_index += field_count;
				mb_offset_index += field_count;
			}

			// SOA fields
			var[soa_kind_off] = cast(u8)bt->Struct.soa_kind;
			if (bt->Struct.soa_kind != StructSoa_None) {
				fb_ti_write_int(var, soa_len_off, bt->Struct.soa_count, 4);
				fb_ti_write_type_info_ptr(m, ti_data_gidx, entry, variant_offset + soa_base_off, var_base + soa_base_off,
				                          ti_data_gidx, bt->Struct.soa_elem, type_info_size);
			}
			break;
		}

		case Type_Map: {
			tag_type = t_type_info_map;
			i64 key_off   = type_offset_of(tag_type, 0);
			i64 value_off = type_offset_of(tag_type, 1);
			// map_info: ^Map_Info — skip for now (requires Phase 11)

			fb_ti_write_type_info_ptr(m, ti_data_gidx, entry, variant_offset + key_off, var_base + key_off,
			                          ti_data_gidx, t->Map.key, type_info_size);
			fb_ti_write_type_info_ptr(m, ti_data_gidx, entry, variant_offset + value_off, var_base + value_off,
			                          ti_data_gidx, t->Map.value, type_info_size);
			break;
		}

		case Type_BitSet: {
			tag_type = t_type_info_bit_set;
			i64 elem_off  = type_offset_of(tag_type, 0);
			i64 under_off = type_offset_of(tag_type, 1);
			i64 lower_off = type_offset_of(tag_type, 2);
			i64 upper_off = type_offset_of(tag_type, 3);

			if (t->BitSet.elem != nullptr) {
				fb_ti_write_type_info_ptr(m, ti_data_gidx, entry, variant_offset + elem_off, var_base + elem_off,
				                          ti_data_gidx, t->BitSet.elem, type_info_size);
			}
			if (t->BitSet.underlying != nullptr) {
				fb_ti_write_type_info_ptr(m, ti_data_gidx, entry, variant_offset + under_off, var_base + under_off,
				                          ti_data_gidx, t->BitSet.underlying, type_info_size);
			}
			fb_ti_write_int(var, lower_off, t->BitSet.lower, 8);
			fb_ti_write_int(var, upper_off, t->BitSet.upper, 8);
			break;
		}

		case Type_SimdVector: {
			tag_type = t_type_info_simd_vector;
			i64 elem_off      = type_offset_of(tag_type, 0);
			i64 elem_size_off = type_offset_of(tag_type, 1);
			i64 count_off     = type_offset_of(tag_type, 2);
			fb_ti_write_type_info_ptr(m, ti_data_gidx, entry, variant_offset + elem_off, var_base + elem_off,
			                          ti_data_gidx, t->SimdVector.elem, type_info_size);
			fb_ti_write_int(var, elem_size_off, type_size_of(t->SimdVector.elem), int_size);
			fb_ti_write_int(var, count_off, t->SimdVector.count, int_size);
			break;
		}

		case Type_Matrix: {
			tag_type = t_type_info_matrix;
			i64 elem_off       = type_offset_of(tag_type, 0);
			i64 elem_size_off  = type_offset_of(tag_type, 1);
			i64 elem_stride_off = type_offset_of(tag_type, 2);
			i64 row_count_off  = type_offset_of(tag_type, 3);
			i64 col_count_off  = type_offset_of(tag_type, 4);
			i64 layout_off     = type_offset_of(tag_type, 5);

			fb_ti_write_type_info_ptr(m, ti_data_gidx, entry, variant_offset + elem_off, var_base + elem_off,
			                          ti_data_gidx, t->Matrix.elem, type_info_size);
			fb_ti_write_int(var, elem_size_off,  type_size_of(t->Matrix.elem), int_size);
			fb_ti_write_int(var, elem_stride_off, matrix_type_stride_in_elems(t), int_size);
			fb_ti_write_int(var, row_count_off,  t->Matrix.row_count, int_size);
			fb_ti_write_int(var, col_count_off,  t->Matrix.column_count, int_size);
			var[layout_off] = t->Matrix.is_row_major ? 1 : 0;
			break;
		}

		case Type_BitField: {
			tag_type = t_type_info_bit_field;
			i64 backing_off    = type_offset_of(tag_type, 0);
			i64 names_off      = type_offset_of(tag_type, 1);
			i64 types_off      = type_offset_of(tag_type, 2);
			i64 bit_sizes_off  = type_offset_of(tag_type, 3);
			i64 bit_offsets_off = type_offset_of(tag_type, 4);
			i64 tags_off       = type_offset_of(tag_type, 5);
			i64 field_count_off = type_offset_of(tag_type, 6);

			Type *bt = base_type(t);
			isize field_count = bt->BitField.fields.count;

			fb_ti_write_type_info_ptr(m, ti_data_gidx, entry, variant_offset + backing_off, var_base + backing_off,
			                          ti_data_gidx, bt->BitField.backing_type, type_info_size);
			fb_ti_write_int(var, field_count_off, field_count, int_size);

			if (field_count > 0) {
				isize base_idx = mb_index;

				// Types
				for (isize i = 0; i < field_count; i++) {
					Entity *f = bt->BitField.fields[i];
					i64 elem_off = (base_idx + i) * ptr_size;
					fb_ti_write_type_info_ptr(m, mb_types_gidx, member_types_buf, elem_off, elem_off,
					                          ti_data_gidx, f->type, type_info_size);
				}

				// Names
				for (isize i = 0; i < field_count; i++) {
					Entity *f = bt->BitField.fields[i];
					i64 elem_off = (base_idx + i) * (ptr_size + int_size);
					fb_ti_write_string(m, mb_names_gidx, member_names_buf, elem_off, elem_off, f->token.string);
				}

				// Bit sizes and bit offsets
				for (isize i = 0; i < field_count; i++) {
					i64 off = (mb_offset_index + i) * int_size;
					fb_ti_write_uint(member_offsets_buf, off, cast(u64)bt->BitField.bit_sizes[i], int_size);
				}
				isize bit_offsets_base = mb_offset_index + field_count;
				for (isize i = 0; i < field_count; i++) {
					i64 off = (bit_offsets_base + i) * int_size;
					fb_ti_write_uint(member_offsets_buf, off, cast(u64)bt->BitField.bit_offsets[i], int_size);
				}

				// Tags
				for (isize i = 0; i < field_count; i++) {
					i64 elem_off = (base_idx + i) * (ptr_size + int_size);
					String tag = {};
					if (bt->BitField.tags != nullptr) {
						tag = bt->BitField.tags[i];
					}
					fb_ti_write_string(m, mb_tags_gidx, member_tags_buf, elem_off, elem_off, tag);
				}

				// Multi-pointer relocs
				{
					fbDataReloc dr = {};
					dr.global_idx   = ti_data_gidx;
					dr.local_offset = cast(u32)(var_base + names_off);
					dr.target_sym   = FB_GLOBAL_SYM_BASE + mb_names_gidx;
					dr.addend       = base_idx * (ptr_size + int_size);
					array_add(&m->data_relocs, dr);
				}
				{
					fbDataReloc dr = {};
					dr.global_idx   = ti_data_gidx;
					dr.local_offset = cast(u32)(var_base + types_off);
					dr.target_sym   = FB_GLOBAL_SYM_BASE + mb_types_gidx;
					dr.addend       = base_idx * ptr_size;
					array_add(&m->data_relocs, dr);
				}
				// bit_sizes → offsets buffer at mb_offset_index
				{
					fbDataReloc dr = {};
					dr.global_idx   = ti_data_gidx;
					dr.local_offset = cast(u32)(var_base + bit_sizes_off);
					dr.target_sym   = FB_GLOBAL_SYM_BASE + mb_offsets_gidx;
					dr.addend       = mb_offset_index * int_size;
					array_add(&m->data_relocs, dr);
				}
				// bit_offsets → offsets buffer at mb_offset_index + field_count
				{
					fbDataReloc dr = {};
					dr.global_idx   = ti_data_gidx;
					dr.local_offset = cast(u32)(var_base + bit_offsets_off);
					dr.target_sym   = FB_GLOBAL_SYM_BASE + mb_offsets_gidx;
					dr.addend       = (mb_offset_index + field_count) * int_size;
					array_add(&m->data_relocs, dr);
				}
				// tags
				{
					fbDataReloc dr = {};
					dr.global_idx   = ti_data_gidx;
					dr.local_offset = cast(u32)(var_base + tags_off);
					dr.target_sym   = FB_GLOBAL_SYM_BASE + mb_tags_gidx;
					dr.addend       = base_idx * (ptr_size + int_size);
					array_add(&m->data_relocs, dr);
				}

				mb_index += field_count;
				mb_offset_index += field_count * 2; // bit_sizes + bit_offsets
			}
			break;
		}

		default:
			break;
		}

		// Write union tag for the variant
		if (tag_type != nullptr) {
			i64 tag_val = union_variant_index(type_info_union, tag_type);
			if (tag_val > 0) {
				fb_ti_write_int(entry, variant_offset + union_tag_offset_within_union,
				                tag_val, ti_union_tag_sz);
			}
		}
	}

	// ── Initialize type_table ───────────────────────────────────────
	// Find the runtime's type_table global and patch its init_data
	{
		Entity *tt_entity = scope_lookup_current(info->runtime_package->scope, str_lit("type_table"));
		if (tt_entity != nullptr) {
			u32 *gidx_ptr = map_get(&m->global_entity_map, tt_entity);
			if (gidx_ptr != nullptr) {
				fbGlobalEntry *ge = &m->global_entries[*gidx_ptr];
				// type_table is a slice: {data: rawptr, len: int} = {ptr, i64}
				i64 slice_size = ptr_size + int_size;
				if (ge->init_data == nullptr) {
					ge->init_data = gb_alloc_array(heap_allocator(), u8, slice_size);
					gb_zero_size(ge->init_data, slice_size);
				}
				// Write len
				fb_ti_write_int(ge->init_data, ptr_size, type_count, int_size);
				// Write data pointer reloc → ti_ptrs
				fbDataReloc dr = {};
				dr.global_idx   = *gidx_ptr;
				dr.local_offset = 0;
				dr.target_sym   = FB_GLOBAL_SYM_BASE + ti_ptrs_gidx;
				dr.addend       = 0;
				array_add(&m->data_relocs, dr);
			}
		}
	}
}
