// Fast Backend — ELF64 relocatable object file emitter
//
// Self-contained ELF definitions — no dependency on system elf.h

// ───────────────────────────────────────────────────────────────────────
// ELF64 type definitions
// ───────────────────────────────────────────────────────────────────────

typedef u16 Elf64_Half;
typedef u32 Elf64_Word;
typedef i32 Elf64_Sword;
typedef u64 Elf64_Xword;
typedef i64 Elf64_Sxword;
typedef u64 Elf64_Addr;
typedef u64 Elf64_Off;

enum : u8 {
	ELFMAG0 = 0x7F, ELFMAG1 = 'E', ELFMAG2 = 'L', ELFMAG3 = 'F',
};

enum : u8 {
	ELFCLASS64   = 2,
	ELFDATA2LSB  = 1,
	EV_CURRENT_B = 1,
	ELFOSABI_NONE = 0,
};

enum : Elf64_Half {
	ET_REL  = 1,
	EM_X86_64 = 62,
};

enum : Elf64_Word {
	EV_CURRENT = 1,
	SHT_NULL     = 0,
	SHT_PROGBITS = 1,
	SHT_SYMTAB   = 2,
	SHT_STRTAB   = 3,
	SHT_RELA     = 4,
	SHT_NOBITS   = 8,
};

enum : Elf64_Xword {
	SHF_WRITE     = 0x1,
	SHF_ALLOC     = 0x2,
	SHF_EXECINSTR = 0x4,
};

enum : u8 {
	STB_LOCAL  = 0,
	STB_GLOBAL = 1,
};

enum : u8 {
	STT_NOTYPE = 0,
	STT_OBJECT = 1,
	STT_FUNC   = 2,
	STT_FILE   = 4,
};

enum : Elf64_Half {
	SHN_UNDEF = 0,
	SHN_ABS   = 0xFFF1,
};

#define ELF64_ST_INFO(b, t) (((b) << 4) | ((t) & 0xF))
#define ELF64_R_INFO(sym, type) (((Elf64_Xword)(sym) << 32) | ((type) & 0xffffffffULL))

// Relocation type constants
enum : Elf64_Word {
	R_X86_64_PC32  = 2,
	R_X86_64_PLT32 = 4,
};

#pragma pack(push, 1)

struct Elf64_Ehdr {
	u8         e_ident[16];
	Elf64_Half e_type;
	Elf64_Half e_machine;
	Elf64_Word e_version;
	Elf64_Addr e_entry;
	Elf64_Off  e_phoff;
	Elf64_Off  e_shoff;
	Elf64_Word e_flags;
	Elf64_Half e_ehsize;
	Elf64_Half e_phentsize;
	Elf64_Half e_phnum;
	Elf64_Half e_shentsize;
	Elf64_Half e_shnum;
	Elf64_Half e_shstrndx;
};

struct Elf64_Shdr {
	Elf64_Word  sh_name;
	Elf64_Word  sh_type;
	Elf64_Xword sh_flags;
	Elf64_Addr  sh_addr;
	Elf64_Off   sh_offset;
	Elf64_Xword sh_size;
	Elf64_Word  sh_link;
	Elf64_Word  sh_info;
	Elf64_Xword sh_addralign;
	Elf64_Xword sh_entsize;
};

struct Elf64_Sym {
	Elf64_Word  st_name;
	u8          st_info;
	u8          st_other;
	Elf64_Half  st_shndx;
	Elf64_Addr  st_value;
	Elf64_Xword st_size;
};

struct Elf64_Rela {
	Elf64_Addr   r_offset;
	Elf64_Xword  r_info;
	Elf64_Sxword r_addend;
};

#pragma pack(pop)

static_assert(sizeof(Elf64_Ehdr) == 64, "ELF header must be 64 bytes");
static_assert(sizeof(Elf64_Shdr) == 64, "Section header must be 64 bytes");
static_assert(sizeof(Elf64_Sym)  == 24, "Symbol entry must be 24 bytes");
static_assert(sizeof(Elf64_Rela) == 24, "Rela entry must be 24 bytes");

// ───────────────────────────────────────────────────────────────────────
// Growable byte buffer for section data
// ───────────────────────────────────────────────────────────────────────

struct fbBuf {
	u8  *data;
	u32  count;
	u32  cap;
};

gb_internal void fb_buf_init(fbBuf *b, u32 initial_cap) {
	b->cap   = initial_cap;
	b->count = 0;
	b->data  = gb_alloc_array(heap_allocator(), u8, initial_cap);
}

gb_internal void fb_buf_free(fbBuf *b) {
	if (b->data) gb_free(heap_allocator(), b->data);
	b->data  = nullptr;
	b->count = 0;
	b->cap   = 0;
}

gb_internal void fb_buf_grow(fbBuf *b, u32 needed) {
	if (b->count + needed <= b->cap) return;
	u32 new_cap = b->cap * 2;
	if (new_cap < b->count + needed) new_cap = b->count + needed;
	b->data = gb_resize_array(heap_allocator(), b->data, b->cap, new_cap);
	b->cap  = new_cap;
}

gb_internal void fb_buf_append(fbBuf *b, void const *src, u32 size) {
	fb_buf_grow(b, size);
	gb_memmove(b->data + b->count, src, size);
	b->count += size;
}

gb_internal void fb_buf_append_byte(fbBuf *b, u8 byte) {
	fb_buf_append(b, &byte, 1);
}

gb_internal u32 fb_buf_append_str(fbBuf *b, char const *s) {
	u32 offset = b->count;
	u32 len = cast(u32)gb_strlen(s) + 1; // include null terminator
	fb_buf_append(b, s, len);
	return offset;
}

gb_internal u32 fb_buf_append_odin_str(fbBuf *b, String s) {
	u32 offset = b->count;
	fb_buf_grow(b, cast(u32)s.len + 1);
	gb_memmove(b->data + b->count, s.text, s.len);
	b->count += cast(u32)s.len;
	fb_buf_append_byte(b, 0);
	return offset;
}

gb_internal void fb_buf_align(fbBuf *b, u32 align) {
	u32 rem = b->count % align;
	if (rem == 0) return;
	u32 pad = align - rem;
	fb_buf_grow(b, pad);
	gb_memset(b->data + b->count, 0, cast(isize)pad);
	b->count += pad;
}

// ───────────────────────────────────────────────────────────────────────
// ELF emitter
// ───────────────────────────────────────────────────────────────────────

enum {
	FB_ELF_SEC_NULL     = 0,
	FB_ELF_SEC_TEXT     = 1,
	FB_ELF_SEC_RODATA   = 2,
	FB_ELF_SEC_DATA     = 3,
	FB_ELF_SEC_BSS      = 4,
	FB_ELF_SEC_SYMTAB   = 5,
	FB_ELF_SEC_STRTAB   = 6,
	FB_ELF_SEC_SHSTRTAB = 7,
	FB_ELF_SEC_RELATEXT = 8,
	FB_ELF_SEC_COUNT    = 9,
};

gb_internal void fb_file_write_padding(gbFile *f, u64 current, u64 target) {
	u8 zeros[64] = {};
	for (u64 rem = target - current; rem > 0; ) {
		u64 chunk = gb_min(rem, 64);
		gb_file_write(f, zeros, cast(isize)chunk);
		rem -= chunk;
	}
}

gb_internal String fb_emit_elf(fbModule *m) {
	u32 proc_count   = cast(u32)m->procs.count;
	u32 rodata_count = cast(u32)m->rodata_entries.count;
	u32 global_count = cast(u32)m->global_entries.count;

	// 1. Build .text section: concatenate all proc machine code
	fbBuf text_buf = {};
	fb_buf_init(&text_buf, 4096);

	u32 *proc_text_offsets = gb_alloc_array(heap_allocator(), u32, proc_count > 0 ? proc_count : 1);

	for_array(i, m->procs) {
		fbProc *p = m->procs[i];
		if (p->is_foreign || p->machine_code_size == 0) {
			proc_text_offsets[i] = 0;
			continue;
		}
		fb_buf_align(&text_buf, 16);
		proc_text_offsets[i] = text_buf.count;
		fb_buf_append(&text_buf, p->machine_code, p->machine_code_size);
	}

	// 2. Build .rodata section: concatenate string literal data
	fbBuf rodata_buf = {};
	fb_buf_init(&rodata_buf, rodata_count > 0 ? 1024 : 4);

	u32 *rodata_offsets = nullptr;
	if (rodata_count > 0) {
		rodata_offsets = gb_alloc_array(heap_allocator(), u32, rodata_count);
		for_array(i, m->rodata_entries) {
			fbRodataEntry *re = &m->rodata_entries[i];
			rodata_offsets[i] = rodata_buf.count;
			fb_buf_append(&rodata_buf, re->data, re->size);
		}
	}

	// 2b. Build .data and .bss sections from global_entries
	fbBuf data_buf = {};
	fb_buf_init(&data_buf, global_count > 0 ? 1024 : 4);

	u32 *global_data_offsets = nullptr;  // offset within .data for initialized globals
	u32 *global_bss_offsets  = nullptr;  // offset within .bss for zero-init globals
	bool *global_is_bss      = nullptr;  // true if this global goes to .bss
	u32 bss_total_size = 0;
	u32 data_max_align = 1;  // max alignment of any .data entry (for sh_addralign)
	u32 bss_max_align  = 1;  // max alignment of any .bss entry (for sh_addralign)

	if (global_count > 0) {
		global_data_offsets = gb_alloc_array(heap_allocator(), u32, global_count);
		global_bss_offsets  = gb_alloc_array(heap_allocator(), u32, global_count);
		global_is_bss       = gb_alloc_array(heap_allocator(), bool, global_count);

		for_array(i, m->global_entries) {
			fbGlobalEntry *ge = &m->global_entries[i];
			if (ge->is_foreign) {
				// Foreign: SHN_UNDEF, offsets unused
				continue;
			}

			if (ge->init_data != nullptr) {
				// .data: constant-initialized
				global_is_bss[i] = false;
				fb_buf_align(&data_buf, ge->align);
				global_data_offsets[i] = data_buf.count;
				fb_buf_append(&data_buf, ge->init_data, ge->size);
				if (ge->align > data_max_align) data_max_align = ge->align;
			} else {
				// .bss: zero-initialized
				global_is_bss[i] = true;
				u32 align = ge->align;
				u32 rem = bss_total_size % align;
				if (rem != 0) bss_total_size += align - rem;
				global_bss_offsets[i] = bss_total_size;
				if (align > bss_max_align) bss_max_align = align;
				bss_total_size += ge->size;
			}
		}
	}

	// 3. Build .strtab and .symtab
	// ELF requires STB_LOCAL before STB_GLOBAL.
	fbBuf strtab = {};
	fb_buf_init(&strtab, 1024);
	fb_buf_append_byte(&strtab, 0);

	u32 local_proc_count  = 0;
	u32 global_proc_count = 0;
	for_array(i, m->procs) {
		fbProc *p = m->procs[i];
		if (p->is_foreign || p->is_export) {
			global_proc_count++;
		} else {
			local_proc_count++;
		}
	}

	// Count local vs global globals
	u32 local_global_count  = 0;
	u32 global_global_count = 0;
	for_array(i, m->global_entries) {
		fbGlobalEntry *ge = &m->global_entries[i];
		if (ge->is_foreign || ge->is_export) {
			global_global_count++;
		} else {
			local_global_count++;
		}
	}

	// Rodata symbols are always local
	u32 total_local  = local_proc_count + rodata_count + local_global_count;
	u32 total_global = global_proc_count + global_global_count;
	u32 actual_sym_count = 2 + total_local + total_global;
	Elf64_Sym *syms = gb_alloc_array(heap_allocator(), Elf64_Sym, actual_sym_count);
	gb_zero_size(syms, sizeof(Elf64_Sym) * actual_sym_count);

	// Entry 0: null (zeroed)
	// Entry 1: file symbol
	{
		String obj_path = fb_filepath_obj(m);
		isize last_slash = -1;
		for (isize j = obj_path.len - 1; j >= 0; j--) {
			if (obj_path.text[j] == '/' || obj_path.text[j] == '\\') {
				last_slash = j;
				break;
			}
		}
		String basename = obj_path;
		if (last_slash >= 0) {
			basename = make_string(obj_path.text + last_slash + 1, obj_path.len - last_slash - 1);
		}
		syms[1].st_name  = fb_buf_append_odin_str(&strtab, basename);
		syms[1].st_info  = ELF64_ST_INFO(STB_LOCAL, STT_FILE);
		syms[1].st_shndx = SHN_ABS;
	}

	u32 local_idx  = 2;
	u32 global_idx = 2 + total_local;

	// Unified abstract-sym → ELF-sym mapping (proc + rodata only; globals use separate array)
	u32 total_abstract = proc_count + rodata_count;
	u32 *sym_elf_idx = gb_alloc_array(heap_allocator(), u32, total_abstract > 0 ? total_abstract : 1);

	// Proc symbols
	for_array(i, m->procs) {
		fbProc *p = m->procs[i];
		u32 idx;
		if (p->is_foreign || p->is_export) {
			idx = global_idx++;
			syms[idx].st_name  = fb_buf_append_odin_str(&strtab, p->name);
			if (p->is_foreign) {
				syms[idx].st_info  = ELF64_ST_INFO(STB_GLOBAL, STT_NOTYPE);
				syms[idx].st_shndx = SHN_UNDEF;
			} else {
				syms[idx].st_info  = ELF64_ST_INFO(STB_GLOBAL, STT_FUNC);
				syms[idx].st_shndx = FB_ELF_SEC_TEXT;
				syms[idx].st_value = proc_text_offsets[i];
				syms[idx].st_size  = p->machine_code_size;
			}
		} else {
			idx = local_idx++;
			syms[idx].st_name  = fb_buf_append_odin_str(&strtab, p->name);
			syms[idx].st_info  = ELF64_ST_INFO(STB_LOCAL, STT_FUNC);
			syms[idx].st_shndx = FB_ELF_SEC_TEXT;
			syms[idx].st_value = proc_text_offsets[i];
			syms[idx].st_size  = p->machine_code_size;
		}
		sym_elf_idx[i] = idx;
	}

	// Rodata symbols (all local)
	for_array(i, m->rodata_entries) {
		fbRodataEntry *re = &m->rodata_entries[i];
		u32 idx = local_idx++;
		syms[idx].st_name  = fb_buf_append_odin_str(&strtab, re->name);
		syms[idx].st_info  = ELF64_ST_INFO(STB_LOCAL, STT_OBJECT);
		syms[idx].st_shndx = FB_ELF_SEC_RODATA;
		syms[idx].st_value = rodata_offsets ? rodata_offsets[i] : 0;
		syms[idx].st_size  = re->size;
		sym_elf_idx[proc_count + i] = idx;
	}

	// Global variable symbols
	// Uses a separate array indexed by global entry index, because global abstract
	// symbol indices use FB_GLOBAL_SYM_BASE + gidx (not contiguous with proc/rodata).
	u32 *global_sym_elf_idx = gb_alloc_array(heap_allocator(), u32, global_count > 0 ? global_count : 1);
	for_array(i, m->global_entries) {
		fbGlobalEntry *ge = &m->global_entries[i];
		u32 idx;
		if (ge->is_foreign || ge->is_export) {
			idx = global_idx++;
			syms[idx].st_name = fb_buf_append_odin_str(&strtab, ge->name);
			if (ge->is_foreign) {
				syms[idx].st_info  = ELF64_ST_INFO(STB_GLOBAL, STT_NOTYPE);
				syms[idx].st_shndx = SHN_UNDEF;
			} else if (global_is_bss && global_is_bss[i]) {
				syms[idx].st_info  = ELF64_ST_INFO(STB_GLOBAL, STT_OBJECT);
				syms[idx].st_shndx = FB_ELF_SEC_BSS;
				syms[idx].st_value = global_bss_offsets[i];
				syms[idx].st_size  = ge->size;
			} else {
				syms[idx].st_info  = ELF64_ST_INFO(STB_GLOBAL, STT_OBJECT);
				syms[idx].st_shndx = FB_ELF_SEC_DATA;
				syms[idx].st_value = global_data_offsets[i];
				syms[idx].st_size  = ge->size;
			}
		} else {
			idx = local_idx++;
			syms[idx].st_name = fb_buf_append_odin_str(&strtab, ge->name);
			if (global_is_bss && global_is_bss[i]) {
				syms[idx].st_info  = ELF64_ST_INFO(STB_LOCAL, STT_OBJECT);
				syms[idx].st_shndx = FB_ELF_SEC_BSS;
				syms[idx].st_value = global_bss_offsets[i];
				syms[idx].st_size  = ge->size;
			} else {
				syms[idx].st_info  = ELF64_ST_INFO(STB_LOCAL, STT_OBJECT);
				syms[idx].st_shndx = FB_ELF_SEC_DATA;
				syms[idx].st_value = global_data_offsets[i];
				syms[idx].st_size  = ge->size;
			}
		}
		global_sym_elf_idx[i] = idx;
	}

	u32 local_sym_count = 2 + total_local;

	// 4. Build .shstrtab
	fbBuf shstrtab = {};
	fb_buf_init(&shstrtab, 128);
	fb_buf_append_byte(&shstrtab, 0);
	u32 shname_text      = fb_buf_append_str(&shstrtab, ".text");
	u32 shname_rodata    = fb_buf_append_str(&shstrtab, ".rodata");
	u32 shname_data      = fb_buf_append_str(&shstrtab, ".data");
	u32 shname_bss       = fb_buf_append_str(&shstrtab, ".bss");
	u32 shname_symtab    = fb_buf_append_str(&shstrtab, ".symtab");
	u32 shname_strtab    = fb_buf_append_str(&shstrtab, ".strtab");
	u32 shname_shstrtab  = fb_buf_append_str(&shstrtab, ".shstrtab");
	u32 shname_relatext  = fb_buf_append_str(&shstrtab, ".rela.text");

	// 5. Calculate layout offsets
	u64 ehdr_size = sizeof(Elf64_Ehdr);

	u64 text_offset = ehdr_size;
	u64 text_size   = text_buf.count;

	// .rodata follows .text
	u64 rodata_offset = text_offset + text_size;
	u64 rodata_size   = rodata_buf.count;
	if (rodata_size > 0 && rodata_offset % 8 != 0) {
		rodata_offset += 8 - (rodata_offset % 8);
	}

	// .data follows .rodata
	u64 data_offset = rodata_offset + rodata_size;
	u64 data_size   = data_buf.count;
	if (data_size > 0 && data_offset % 8 != 0) {
		data_offset += 8 - (data_offset % 8);
	}

	// .bss is NOBITS — no file bytes, but needs sh_size
	u64 bss_size = bss_total_size;

	// .symtab follows .data
	u64 symtab_offset = data_offset + data_size;
	if (symtab_offset % 8 != 0) symtab_offset += 8 - (symtab_offset % 8);
	u64 symtab_size = cast(u64)actual_sym_count * sizeof(Elf64_Sym);

	u64 strtab_offset = symtab_offset + symtab_size;
	u64 strtab_size   = strtab.count;

	u64 shstrtab_offset = strtab_offset + strtab_size;
	u64 shstrtab_size   = shstrtab.count;

	// 6. Build .rela.text
	fbBuf rela_buf = {};
	fb_buf_init(&rela_buf, 256);
	for_array(pi, m->procs) {
		fbProc *p = m->procs[pi];
		if (p->is_foreign || p->reloc_count == 0) continue;
		for (u32 ri = 0; ri < p->reloc_count; ri++) {
			fbReloc *rel = &p->relocs[ri];
			Elf64_Rela rela = {};
			rela.r_offset = proc_text_offsets[pi] + rel->code_offset;
			Elf64_Word elf_type = (rel->reloc_type == FB_RELOC_PLT32) ? R_X86_64_PLT32 : R_X86_64_PC32;
			// Map abstract symbol index to ELF symbol index.
			// Global variables use FB_GLOBAL_SYM_BASE + gidx; everything else is in sym_elf_idx.
			u32 elf_sym;
			if (rel->target_sym >= FB_GLOBAL_SYM_BASE) {
				u32 gidx = rel->target_sym - FB_GLOBAL_SYM_BASE;
				GB_ASSERT(gidx < global_count);
				elf_sym = global_sym_elf_idx[gidx];
			} else {
				elf_sym = sym_elf_idx[rel->target_sym];
			}
			rela.r_info   = ELF64_R_INFO(elf_sym, elf_type);
			rela.r_addend = rel->addend;
			fb_buf_append(&rela_buf, &rela, sizeof(Elf64_Rela));
		}
	}

	u64 relatext_offset = shstrtab_offset + shstrtab_size;
	u64 relatext_size   = rela_buf.count;
	if (relatext_size > 0) {
		if (relatext_offset % 8 != 0) relatext_offset += 8 - (relatext_offset % 8);
	}

	u64 shdr_offset = relatext_offset + relatext_size;
	if (shdr_offset % 8 != 0) shdr_offset += 8 - (shdr_offset % 8);

	// 7. Section headers
	Elf64_Shdr shdrs[FB_ELF_SEC_COUNT] = {};

	shdrs[FB_ELF_SEC_TEXT].sh_name      = shname_text;
	shdrs[FB_ELF_SEC_TEXT].sh_type      = SHT_PROGBITS;
	shdrs[FB_ELF_SEC_TEXT].sh_flags     = SHF_ALLOC | SHF_EXECINSTR;
	shdrs[FB_ELF_SEC_TEXT].sh_offset    = text_offset;
	shdrs[FB_ELF_SEC_TEXT].sh_size      = text_size;
	shdrs[FB_ELF_SEC_TEXT].sh_addralign = 16;

	shdrs[FB_ELF_SEC_RODATA].sh_name      = shname_rodata;
	shdrs[FB_ELF_SEC_RODATA].sh_type      = SHT_PROGBITS;
	shdrs[FB_ELF_SEC_RODATA].sh_flags     = SHF_ALLOC;
	shdrs[FB_ELF_SEC_RODATA].sh_offset    = rodata_offset;
	shdrs[FB_ELF_SEC_RODATA].sh_size      = rodata_size;
	shdrs[FB_ELF_SEC_RODATA].sh_addralign = 8;

	shdrs[FB_ELF_SEC_DATA].sh_name      = shname_data;
	shdrs[FB_ELF_SEC_DATA].sh_type      = SHT_PROGBITS;
	shdrs[FB_ELF_SEC_DATA].sh_flags     = SHF_ALLOC | SHF_WRITE;
	shdrs[FB_ELF_SEC_DATA].sh_offset    = data_offset;
	shdrs[FB_ELF_SEC_DATA].sh_size      = data_size;
	shdrs[FB_ELF_SEC_DATA].sh_addralign = data_max_align > 8 ? data_max_align : 8;

	shdrs[FB_ELF_SEC_BSS].sh_name      = shname_bss;
	shdrs[FB_ELF_SEC_BSS].sh_type      = SHT_NOBITS;
	shdrs[FB_ELF_SEC_BSS].sh_flags     = SHF_ALLOC | SHF_WRITE;
	shdrs[FB_ELF_SEC_BSS].sh_offset    = data_offset + data_size; // same file offset (no bytes)
	shdrs[FB_ELF_SEC_BSS].sh_size      = bss_size;
	shdrs[FB_ELF_SEC_BSS].sh_addralign = bss_max_align > 8 ? bss_max_align : 8;

	shdrs[FB_ELF_SEC_SYMTAB].sh_name      = shname_symtab;
	shdrs[FB_ELF_SEC_SYMTAB].sh_type      = SHT_SYMTAB;
	shdrs[FB_ELF_SEC_SYMTAB].sh_offset    = symtab_offset;
	shdrs[FB_ELF_SEC_SYMTAB].sh_size      = symtab_size;
	shdrs[FB_ELF_SEC_SYMTAB].sh_link      = FB_ELF_SEC_STRTAB;
	shdrs[FB_ELF_SEC_SYMTAB].sh_info      = local_sym_count;
	shdrs[FB_ELF_SEC_SYMTAB].sh_addralign = 8;
	shdrs[FB_ELF_SEC_SYMTAB].sh_entsize   = sizeof(Elf64_Sym);

	shdrs[FB_ELF_SEC_STRTAB].sh_name      = shname_strtab;
	shdrs[FB_ELF_SEC_STRTAB].sh_type      = SHT_STRTAB;
	shdrs[FB_ELF_SEC_STRTAB].sh_offset    = strtab_offset;
	shdrs[FB_ELF_SEC_STRTAB].sh_size      = strtab_size;
	shdrs[FB_ELF_SEC_STRTAB].sh_addralign = 1;

	shdrs[FB_ELF_SEC_SHSTRTAB].sh_name      = shname_shstrtab;
	shdrs[FB_ELF_SEC_SHSTRTAB].sh_type      = SHT_STRTAB;
	shdrs[FB_ELF_SEC_SHSTRTAB].sh_offset    = shstrtab_offset;
	shdrs[FB_ELF_SEC_SHSTRTAB].sh_size      = shstrtab_size;
	shdrs[FB_ELF_SEC_SHSTRTAB].sh_addralign = 1;

	shdrs[FB_ELF_SEC_RELATEXT].sh_name      = shname_relatext;
	shdrs[FB_ELF_SEC_RELATEXT].sh_type      = SHT_RELA;
	shdrs[FB_ELF_SEC_RELATEXT].sh_offset    = relatext_offset;
	shdrs[FB_ELF_SEC_RELATEXT].sh_size      = relatext_size;
	shdrs[FB_ELF_SEC_RELATEXT].sh_link      = FB_ELF_SEC_SYMTAB;
	shdrs[FB_ELF_SEC_RELATEXT].sh_info      = FB_ELF_SEC_TEXT;
	shdrs[FB_ELF_SEC_RELATEXT].sh_addralign = 8;
	shdrs[FB_ELF_SEC_RELATEXT].sh_entsize   = sizeof(Elf64_Rela);

	// 8. ELF header
	Elf64_Ehdr ehdr = {};
	ehdr.e_ident[0]  = ELFMAG0;
	ehdr.e_ident[1]  = ELFMAG1;
	ehdr.e_ident[2]  = ELFMAG2;
	ehdr.e_ident[3]  = ELFMAG3;
	ehdr.e_ident[4]  = ELFCLASS64;
	ehdr.e_ident[5]  = ELFDATA2LSB;
	ehdr.e_ident[6]  = EV_CURRENT_B;
	ehdr.e_ident[7]  = ELFOSABI_NONE;
	ehdr.e_type      = ET_REL;
	ehdr.e_machine   = EM_X86_64;
	ehdr.e_version   = EV_CURRENT;
	ehdr.e_shoff     = shdr_offset;
	ehdr.e_ehsize    = sizeof(Elf64_Ehdr);
	ehdr.e_shentsize = sizeof(Elf64_Shdr);
	ehdr.e_shnum     = FB_ELF_SEC_COUNT;
	ehdr.e_shstrndx  = FB_ELF_SEC_SHSTRTAB;

	// 9. Write to file
	String filepath = fb_filepath_obj(m);
	char *filepath_cstr = alloc_cstring(heap_allocator(), filepath);

	gbFile f = {};
	gbFileError ferr = gb_file_create(&f, filepath_cstr);
	if (ferr != gbFileError_None) {
		gb_printf_err("fast backend: failed to create object file '%s'\n", filepath_cstr);
		gb_free(heap_allocator(), filepath_cstr);
		fb_buf_free(&text_buf);
		fb_buf_free(&rodata_buf);
		fb_buf_free(&data_buf);
		fb_buf_free(&strtab);
		fb_buf_free(&shstrtab);
		fb_buf_free(&rela_buf);
		gb_free(heap_allocator(), syms);
		gb_free(heap_allocator(), proc_text_offsets);
		if (rodata_offsets) gb_free(heap_allocator(), rodata_offsets);
		if (global_data_offsets) gb_free(heap_allocator(), global_data_offsets);
		if (global_bss_offsets)  gb_free(heap_allocator(), global_bss_offsets);
		if (global_is_bss)       gb_free(heap_allocator(), global_is_bss);
		gb_free(heap_allocator(), sym_elf_idx);
		gb_free(heap_allocator(), global_sym_elf_idx);
		return {};
	}

	gb_file_write(&f, &ehdr, sizeof(ehdr));

	if (text_buf.count > 0) {
		gb_file_write(&f, text_buf.data, text_buf.count);
	}

	// .rodata
	if (rodata_buf.count > 0) {
		fb_file_write_padding(&f, text_offset + text_size, rodata_offset);
		gb_file_write(&f, rodata_buf.data, rodata_buf.count);
	}

	// .data
	if (data_buf.count > 0) {
		fb_file_write_padding(&f, rodata_offset + rodata_size, data_offset);
		gb_file_write(&f, data_buf.data, data_buf.count);
	}

	// .bss: NOBITS — no file data written

	// .symtab
	fb_file_write_padding(&f, data_offset + data_size, symtab_offset);
	gb_file_write(&f, syms, sizeof(Elf64_Sym) * actual_sym_count);

	gb_file_write(&f, strtab.data, strtab.count);
	gb_file_write(&f, shstrtab.data, shstrtab.count);

	if (rela_buf.count > 0) {
		fb_file_write_padding(&f, shstrtab_offset + shstrtab_size, relatext_offset);
		gb_file_write(&f, rela_buf.data, rela_buf.count);
	}

	fb_file_write_padding(&f, relatext_offset + relatext_size, shdr_offset);
	gb_file_write(&f, shdrs, sizeof(shdrs));

	gb_file_close(&f);

	gb_free(heap_allocator(), filepath_cstr);
	fb_buf_free(&text_buf);
	fb_buf_free(&rodata_buf);
	fb_buf_free(&data_buf);
	fb_buf_free(&strtab);
	fb_buf_free(&shstrtab);
	fb_buf_free(&rela_buf);
	gb_free(heap_allocator(), syms);
	gb_free(heap_allocator(), proc_text_offsets);
	if (rodata_offsets) gb_free(heap_allocator(), rodata_offsets);
	if (global_data_offsets) gb_free(heap_allocator(), global_data_offsets);
	if (global_bss_offsets)  gb_free(heap_allocator(), global_bss_offsets);
	if (global_is_bss)       gb_free(heap_allocator(), global_is_bss);
	gb_free(heap_allocator(), sym_elf_idx);
	gb_free(heap_allocator(), global_sym_elf_idx);

	return filepath;
}

gb_internal String fb_emit_object(fbModule *m) {
	switch (m->target.os) {
	case FB_OS_LINUX:
	case FB_OS_FREEBSD:
		return fb_emit_elf(m);
	default:
		gb_printf_err("fast backend: unsupported target OS for object emission\n");
		return {};
	}
}
