// Fast Backend IR — module lifecycle, type helpers, instruction emission,
// procedure lifecycle, name mangling, code generation orchestration

// Maps Odin Type* to fbType (machine-level scalar kind).
// Returns FB_VOID for aggregate types (structs, arrays, etc.) that live only in memory.
gb_internal fbType fb_data_type(Type *t) {
	GB_ASSERT(t != nullptr);
	t = core_type(t);
	i64 sz = type_size_of(t);
	switch (t->kind) {
	case Type_Basic:
		switch (t->Basic.kind) {
		// Boolean types — explicit mapping by size
		case Basic_bool:
		case Basic_b8:   return FB_I8;
		case Basic_b16:  return FB_I16;
		case Basic_b32:  return FB_I32;
		case Basic_b64:  return FB_I64;

		case Basic_i8:
		case Basic_u8:
		case Basic_i16:
		case Basic_u16:
		case Basic_i32:
		case Basic_u32:
		case Basic_i64:
		case Basic_u64:
		case Basic_i128:
		case Basic_u128:

		case Basic_rune:

		case Basic_int:
		case Basic_uint:
		case Basic_uintptr:
		case Basic_typeid:
			switch (sz) {
			case 1:  return FB_I8;
			case 2:  return FB_I16;
			case 4:  return FB_I32;
			case 8:  return FB_I64;
			case 16: return FB_I128;
			}
			return FB_VOID;

		case Basic_f16: return FB_F16;
		case Basic_f32: return FB_F32;
		case Basic_f64: return FB_F64;

		case Basic_rawptr:  return FB_PTR;
		case Basic_cstring: return FB_PTR;

		// Endian-specific integer types
		case Basic_i16le: case Basic_u16le:
		case Basic_i32le: case Basic_u32le:
		case Basic_i64le: case Basic_u64le:
		case Basic_i128le: case Basic_u128le:
		case Basic_i16be: case Basic_u16be:
		case Basic_i32be: case Basic_u32be:
		case Basic_i64be: case Basic_u64be:
		case Basic_i128be: case Basic_u128be:
			switch (sz) {
			case 1:  return FB_I8;
			case 2:  return FB_I16;
			case 4:  return FB_I32;
			case 8:  return FB_I64;
			case 16: return FB_I128;
			}
			return FB_VOID;

		// Endian-specific float types
		case Basic_f16le: case Basic_f16be: return FB_F16;
		case Basic_f32le: case Basic_f32be: return FB_F32;
		case Basic_f64le: case Basic_f64be: return FB_F64;
		}
		break;

	case Type_Pointer:
	case Type_MultiPointer:
	case Type_Proc:
		return FB_PTR;

	case Type_BitSet:
		return fb_data_type(bit_set_to_int(t));

	case Type_Enum:
		return fb_data_type(t->Enum.base_type);
	}

	return FB_VOID;
}

gb_internal i32 fb_type_size(fbType t) {
	switch (t.kind) {
	case FBT_VOID: return 0;
	case FBT_I1:   return 1;
	case FBT_I8:   return 1;
	case FBT_I16:  return 2;
	case FBT_I32:  return 4;
	case FBT_I64:  return 8;
	case FBT_I128: return 16;
	case FBT_F16:  return 2;
	case FBT_F32:  return 4;
	case FBT_F64:  return 8;
	case FBT_PTR:  return 8; // 64-bit targets only for now
	default:       return 0;
	}
}

gb_internal i32 fb_type_align(fbType t) {
	i32 sz = fb_type_size(t);
	if (t.lanes > 0) {
		i32 total = sz * cast(i32)t.lanes;
		i32 align = cast(i32)next_pow2(cast(i64)total);
		i32 max_align = cast(i32)build_context.max_simd_align;
		return gb_min(align, max_align);
	}
	return sz;
}

gb_internal bool fb_type_is_float(fbType t) {
	return t.kind == FBT_F16 || t.kind == FBT_F32 || t.kind == FBT_F64;
}

gb_internal bool fb_type_is_integer(fbType t) {
	return t.kind >= FBT_I1 && t.kind <= FBT_I128;
}

// ───────────────────────────────────────────────────────────────────────
// Target helpers
// ───────────────────────────────────────────────────────────────────────

gb_internal fbArch fb_arch_from_target(TargetArchKind arch) {
	switch (arch) {
	case TargetArch_amd64: return FB_ARCH_X64;
	case TargetArch_arm64: return FB_ARCH_ARM64;
	default:               return FB_ARCH_UNKNOWN;
	}
}

gb_internal fbOS fb_os_from_target(TargetOsKind os) {
	switch (os) {
	case TargetOs_linux:   return FB_OS_LINUX;
	case TargetOs_windows: return FB_OS_WINDOWS;
	case TargetOs_darwin:  return FB_OS_MACOS;
	case TargetOs_freebsd: return FB_OS_FREEBSD;
	default:               return FB_OS_UNKNOWN;
	}
}

// ───────────────────────────────────────────────────────────────────────
// Instruction emission helpers
// ───────────────────────────────────────────────────────────────────────

gb_internal bool fb_op_has_result(fbOp op) {
	switch (op) {
	case FB_STORE:
	case FB_MEMCPY:
	case FB_MEMSET:
	case FB_MEMZERO:
	case FB_JUMP:
	case FB_BRANCH:
	case FB_SWITCH:
	case FB_RET:
	case FB_UNREACHABLE:
	case FB_TRAP:
	case FB_DEBUGBREAK:
	case FB_ATOMIC_STORE:
	case FB_TAILCALL:
	case FB_FENCE:
	case FB_VA_START:
	case FB_PREFETCH:
	case FB_ASM:
		return false;
	default:
		return true;
	}
}

gb_internal u32 fb_inst_emit(fbProc *p, fbOp op, fbType type,
                              u32 a, u32 b, u32 c, u32 loc, i64 imm) {
	GB_ASSERT_MSG(p->current_block < p->block_count,
		"fb_inst_emit: no active block");

	if (p->inst_count >= p->inst_cap) {
		u32 new_cap = p->inst_cap * 2;
		if (new_cap < 64) new_cap = 64;
		p->insts = gb_resize_array(heap_allocator(), p->insts, p->inst_cap, new_cap);
		p->inst_cap = new_cap;
	}

	// type.kind != FBT_VOID: ops like FB_CALL with a void return have
	// fb_op_has_result()==true but should not allocate a value number.
	u32 r = (fb_op_has_result(op) && type.kind != FBT_VOID) ? p->next_value++ : FB_NOREG;

	fbInst *inst = &p->insts[p->inst_count];
	inst->op       = cast(u8)op;
	inst->flags    = 0;
	inst->type_raw = fb_type_pack(type);
	inst->r        = r;
	inst->a        = a;
	inst->b        = b;
	inst->c        = c;
	inst->loc      = loc;
	inst->imm      = imm;

	p->inst_count++;
	p->blocks[p->current_block].inst_count++;

	return r;
}

gb_internal u32 fb_block_create(fbProc *p) {
	if (p->block_count >= p->block_cap) {
		u32 new_cap = p->block_cap * 2;
		if (new_cap < 8) new_cap = 8;
		p->blocks = gb_resize_array(heap_allocator(), p->blocks, p->block_cap, new_cap);
		p->block_cap = new_cap;
	}

	u32 id = p->block_count++;
	p->blocks[id].first_inst  = UINT32_MAX; // sentinel until fb_block_start
	p->blocks[id].inst_count  = 0;
	return id;
}

gb_internal void fb_block_start(fbProc *p, u32 block_id) {
	GB_ASSERT(block_id < p->block_count);
	p->current_block = block_id;
	p->blocks[block_id].first_inst = p->inst_count;
}

gb_internal u32 fb_slot_create(fbProc *p, u32 size, u32 align, Entity *entity, Type *odin_type) {
	if (p->slot_count >= p->slot_cap) {
		u32 new_cap = p->slot_cap * 2;
		if (new_cap < 16) new_cap = 16;
		p->slots = gb_resize_array(heap_allocator(), p->slots, p->slot_cap, new_cap);
		p->slot_cap = new_cap;
	}

	u32 idx = p->slot_count++;
	fbStackSlot *s = &p->slots[idx];
	s->size         = size;
	s->align        = align;
	s->frame_offset = 0; // assigned during lowering
	s->entity       = entity;
	s->odin_type    = odin_type;
	s->scope_start  = p->inst_count;
	return idx;
}

gb_internal u32 fb_aux_push(fbProc *p, u32 val) {
	if (p->aux_count >= p->aux_cap) {
		u32 new_cap = p->aux_cap * 2;
		if (new_cap < 32) new_cap = 32;
		p->aux = gb_resize_array(heap_allocator(), p->aux, p->aux_cap, new_cap);
		p->aux_cap = new_cap;
	}

	u32 idx = p->aux_count++;
	p->aux[idx] = val;
	return idx;
}

// ───────────────────────────────────────────────────────────────────────
// Procedure lifecycle
//
// Allocator strategy: the fbProc struct itself is allocated from
// permanent_allocator (outlives the builder, needed through emission).
// Internal arrays (insts, blocks, slots, aux, locs) use heap_allocator
// and are freed in fb_proc_destroy. This split is intentional.
// ───────────────────────────────────────────────────────────────────────

gb_internal fbProc *fb_proc_create(fbModule *m, Entity *e) {
	fbProc *p = gb_alloc_item(permanent_allocator(), fbProc);
	gb_zero_item(p);

	p->entity    = e;
	p->odin_type = e->type;
	p->name      = fb_get_entity_name(m, e);

	p->is_foreign = e->Procedure.is_foreign;
	p->is_export  = e->Procedure.is_export;

	p->current_block = FB_NOREG; // no active block until fb_block_start
	p->split_returns_index = -1;

	// Foreign procs are extern declarations — no IR, no machine code.
	// Skip heap allocations; all pointers remain NULL, caps stay 0.
	if (!p->is_foreign) {
		p->inst_cap  = 64;
		p->insts     = gb_alloc_array(heap_allocator(), fbInst, p->inst_cap);

		p->block_cap = 8;
		p->blocks    = gb_alloc_array(heap_allocator(), fbBlock, p->block_cap);

		p->slot_cap  = 16;
		p->slots     = gb_alloc_array(heap_allocator(), fbStackSlot, p->slot_cap);

		p->aux_cap   = 32;
		p->aux       = gb_alloc_array(heap_allocator(), u32, p->aux_cap);

		p->loc_cap   = 16;
		p->locs      = gb_alloc_array(heap_allocator(), fbLoc, p->loc_cap);
	}

	return p;
}

gb_internal void fb_proc_destroy(fbProc *p) {
	if (p->insts)        gb_free(heap_allocator(), p->insts);
	if (p->blocks)       gb_free(heap_allocator(), p->blocks);
	if (p->slots)        gb_free(heap_allocator(), p->slots);
	if (p->aux)          gb_free(heap_allocator(), p->aux);
	if (p->locs)         gb_free(heap_allocator(), p->locs);
	if (p->param_locs)   gb_free(heap_allocator(), p->param_locs);
	if (p->relocs)       gb_free(heap_allocator(), p->relocs);
	if (p->machine_code) gb_free(heap_allocator(), p->machine_code);
}

// ───────────────────────────────────────────────────────────────────────
// Name mangling (mirrors cg_mangle_name / cg_get_entity_name from tilde.cpp)
// ───────────────────────────────────────────────────────────────────────

#ifndef FB_PKG_NAME_SEPARATOR
#define FB_PKG_NAME_SEPARATOR "."
#endif

gb_internal String fb_mangle_name(fbModule *m, Entity *e) {
	gb_unused(m);
	String name = e->token.string;

	AstPackage *pkg = e->pkg;
	GB_ASSERT_MSG(pkg != nullptr, "Missing package for '%.*s'", LIT(name));
	String pkgn = pkg->name;
	GB_ASSERT(!rune_is_digit(pkgn[0]));

	isize max_len = pkgn.len + 1 + name.len + 1;
	bool require_suffix_id = is_type_polymorphic(e->type, true);

	if ((e->scope->flags & (ScopeFlag_File | ScopeFlag_Pkg)) == 0) {
		require_suffix_id = true;
	} else if (is_blank_ident(e->token)) {
		require_suffix_id = true;
	}
	if (e->flags & EntityFlag_NotExported) {
		require_suffix_id = true;
	}

	if (require_suffix_id) {
		max_len += 21;
	}

	char *new_name = gb_alloc_array(permanent_allocator(), char, max_len);
	isize new_name_len = gb_snprintf(
		new_name, max_len,
		"%.*s" FB_PKG_NAME_SEPARATOR "%.*s", LIT(pkgn), LIT(name)
	);
	if (require_suffix_id) {
		char *str = new_name + new_name_len-1;
		isize len = max_len-new_name_len;
		// %llu is the codebase-wide portable pattern for printing u64 values
		isize extra = gb_snprintf(str, len, "-%llu", cast(unsigned long long)e->id);
		new_name_len += extra-1;
	}

	return make_string(cast(u8 const *)new_name, new_name_len-1);
}

gb_internal String fb_get_entity_name(fbModule *m, Entity *e) {
	GB_ASSERT(e != nullptr);

	if (e->pkg == nullptr) {
		return e->token.string;
	}

	if (e->kind == Entity_Procedure && e->Procedure.link_name.len > 0) {
		return e->Procedure.link_name;
	}

	bool no_name_mangle = false;
	if (e->kind == Entity_Procedure && e->Procedure.is_export) {
		no_name_mangle = true;
	}
	if (e->kind == Entity_Variable) {
		no_name_mangle = e->Variable.link_name.len > 0 || e->Variable.is_foreign || e->Variable.is_export;
		if (e->Variable.link_name.len > 0) {
			return e->Variable.link_name;
		}
	}

	String name = {};
	if (!no_name_mangle) {
		name = fb_mangle_name(m, e);
	}
	if (name.len == 0) {
		name = e->token.string;
	}

	if (e->kind == Entity_Procedure) {
		e->Procedure.link_name = name;
	}

	return name;
}

// ───────────────────────────────────────────────────────────────────────
// Object file path (mirrors cg_filepath_obj_for_module from tilde.cpp)
// ───────────────────────────────────────────────────────────────────────

gb_internal String fb_filepath_obj(fbModule *m) {
	gb_unused(m);
	String path = concatenate3_strings(permanent_allocator(),
		build_context.build_paths[BuildPath_Output].basename,
		STR_LIT("/"),
		build_context.build_paths[BuildPath_Output].name
	);

	String ext = {};
	switch (build_context.metrics.os) {
	case TargetOs_windows:
		ext = STR_LIT(".obj");
		break;
	default:
	case TargetOs_darwin:
	case TargetOs_linux:
	case TargetOs_freebsd:
		ext = STR_LIT(".o");
		break;
	case TargetOs_freestanding:
		switch (build_context.metrics.abi) {
		default:
		case TargetABI_Default:
		case TargetABI_SysV:
			ext = STR_LIT(".o");
			break;
		case TargetABI_Win64:
			ext = STR_LIT(".obj");
			break;
		}
		break;
	}

	return concatenate_strings(permanent_allocator(), path, ext);
}

// ───────────────────────────────────────────────────────────────────────
// Module lifecycle
// ───────────────────────────────────────────────────────────────────────

gb_internal fbModule *fb_module_create(Checker *c) {
	fbModule *m = gb_alloc_item(permanent_allocator(), fbModule);

	m->checker = c;
	m->info    = &c->info;

	m->target.arch     = fb_arch_from_target(build_context.metrics.arch);
	m->target.os       = fb_os_from_target(build_context.metrics.os);
	m->target.ptr_size = cast(u8)build_context.metrics.ptr_size;
	m->target.int_size = cast(u8)build_context.metrics.int_size;
	m->target.features = 0; // populated in future phases

	string_map_init(&m->symbol_map);
	string_map_init(&m->string_intern_map);
	map_init(&m->file_id_to_idx);

	array_init(&m->procs, heap_allocator());
	array_init(&m->symbols, heap_allocator());
	array_init(&m->rodata_entries, heap_allocator());
	array_init(&m->global_entries, heap_allocator());
	map_init(&m->global_entity_map);
	array_init(&m->source_files, heap_allocator());

	// Register source files
	for_array(id, global_files) {
		if (AstFile *f = global_files[id]) {
			fbSourceFile sf = {};
			sf.path = f->fullpath;
			sf.id   = cast(u32)id;
			u32 idx = cast(u32)m->source_files.count;
			array_add(&m->source_files, sf);
			map_set(&m->file_id_to_idx, cast(uintptr)id, idx);
		}
	}

	return m;
}

gb_internal void fb_module_destroy(fbModule *m) {
	for_array(i, m->procs) {
		fb_proc_destroy(m->procs[i]);
	}

	for_array(i, m->rodata_entries) {
		if (m->rodata_entries[i].data) {
			gb_free(heap_allocator(), m->rodata_entries[i].data);
		}
	}

	for_array(i, m->global_entries) {
		if (m->global_entries[i].init_data) {
			gb_free(heap_allocator(), m->global_entries[i].init_data);
		}
	}

	string_map_destroy(&m->symbol_map);
	string_map_destroy(&m->string_intern_map);
	map_destroy(&m->file_id_to_idx);
	map_destroy(&m->global_entity_map);

	array_free(&m->procs);
	array_free(&m->symbols);
	array_free(&m->rodata_entries);
	array_free(&m->global_entries);
	array_free(&m->source_files);
}

// Intern a string literal into the module's rodata section.
// Returns the abstract symbol index (procs.count + rodata entry index).
// Deduplicates identical strings.
gb_internal u32 fb_module_intern_string_data(fbModule *m, String str) {
	// Check for existing entry
	u32 *existing = string_map_get(&m->string_intern_map, str);
	if (existing != nullptr) {
		return FB_RODATA_SYM_BASE + *existing;
	}

	// Create new rodata entry with null-terminated copy
	u32 rodata_idx = cast(u32)m->rodata_entries.count;

	fbRodataEntry entry = {};
	entry.size = cast(u32)str.len + 1; // +1 for null terminator (for cstring compat)
	entry.data = gb_alloc_array(heap_allocator(), u8, entry.size);
	if (str.len > 0) {
		gb_memmove(entry.data, str.text, str.len);
	}
	entry.data[str.len] = 0; // null terminator

	// Generate a unique symbol name
	char name_buf[64];
	gb_snprintf(name_buf, sizeof(name_buf), ".L.str.%u", rodata_idx);
	isize name_len = gb_strlen(name_buf);
	u8 *name_copy = gb_alloc_array(permanent_allocator(), u8, name_len);
	gb_memmove(name_copy, name_buf, name_len);
	entry.name = make_string(name_copy, name_len);

	array_add(&m->rodata_entries, entry);
	string_map_set(&m->string_intern_map, str, rodata_idx);

	return FB_RODATA_SYM_BASE + rodata_idx;
}

// ───────────────────────────────────────────────────────────────────────
// Code generation entry point
// ───────────────────────────────────────────────────────────────────────

gb_internal bool fb_generate_code(Checker *c, LinkerData *ld) {
	linker_data_init(ld, &c->info, c->parser->init_fullpath);

	fbModule *m = fb_module_create(c);
	m->linker_data = ld;

	if (m->target.arch != FB_ARCH_X64) {
		gb_printf_err("fast backend: only x86-64 is supported (got %s)\n",
			target_arch_names[build_context.metrics.arch]);
		fb_module_destroy(m);
		return false;
	}

	fb_generate_procedures(m);

	// Enumerate foreign libraries for the linker
	for (Entity *e : m->info->required_foreign_imports_through_force) {
		if (e == nullptr) continue;
		GB_ASSERT(e->kind == Entity_LibraryName);
		if (!ptr_set_update(&ld->foreign_libraries_set, e)) {
			array_add(&ld->foreign_libraries, e);
		}
	}

#if defined(GB_SYSTEM_OSX)
	linker_enable_system_library_linking(ld);
#endif

	fb_lower_all(m);

	String obj = fb_emit_object(m);
	if (obj.len == 0) {
		fb_module_destroy(m);
		return false;
	}
	array_add(&ld->output_object_paths, obj);

	fb_module_destroy(m);
	return true;
}
