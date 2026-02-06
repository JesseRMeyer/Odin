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
};

enum : Elf64_Xword {
	SHF_ALLOC     = 0x2,
	SHF_EXECINSTR = 0x4,
};

enum : u8 {
	STB_LOCAL  = 0,
	STB_GLOBAL = 1,
};

enum : u8 {
	STT_NOTYPE = 0,
	STT_FUNC   = 2,
	STT_FILE   = 4,
};

enum : Elf64_Half {
	SHN_UNDEF = 0,
	SHN_ABS   = 0xFFF1,
};

#define ELF64_ST_INFO(b, t) (((b) << 4) | ((t) & 0xF))

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

// Section indices — Phase 2 sections only.
// Future phases add .data, .bss, .rodata using the existing fbSymbol fields
// (init_data, is_read_only, etc.) to determine section placement.
enum {
	FB_ELF_SEC_NULL     = 0,
	FB_ELF_SEC_TEXT     = 1,
	FB_ELF_SEC_SYMTAB   = 2,
	FB_ELF_SEC_STRTAB   = 3,
	FB_ELF_SEC_SHSTRTAB = 4,
	FB_ELF_SEC_RELATEXT = 5,
	FB_ELF_SEC_COUNT    = 6,
};

gb_internal String fb_emit_elf(fbModule *m) {
	// 1. Build .text section: concatenate all proc machine code
	fbBuf text_buf = {};
	fb_buf_init(&text_buf, 4096);

	// Track per-proc offset within .text
	u32 *proc_text_offsets = gb_alloc_array(heap_allocator(), u32, m->procs.count);

	for_array(i, m->procs) {
		fbProc *p = m->procs[i];
		if (p->is_foreign || p->machine_code_size == 0) {
			proc_text_offsets[i] = 0;
			continue;
		}
		// Align to 16 bytes for function entries
		fb_buf_align(&text_buf, 16);
		proc_text_offsets[i] = text_buf.count;
		fb_buf_append(&text_buf, p->machine_code, p->machine_code_size);
	}

	// 2. Build .strtab (symbol name strings)
	fbBuf strtab = {};
	fb_buf_init(&strtab, 1024);
	fb_buf_append_byte(&strtab, 0); // first byte must be null

	// 3. Build .symtab
	// Count symbols: null + file + one per proc
	u32 sym_count = 2 + cast(u32)m->procs.count; // null + file + procs
	Elf64_Sym *syms = gb_alloc_array(heap_allocator(), Elf64_Sym, sym_count);
	gb_zero_size(syms, sizeof(Elf64_Sym) * sym_count);

	// Entry 0: null symbol (already zeroed)

	// Entry 1: file symbol
	{
		String obj_path = fb_filepath_obj(m);
		// Extract basename for file symbol
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

		char *fname = gb_alloc_array(heap_allocator(), char, basename.len + 1);
		gb_memmove(fname, basename.text, basename.len);
		fname[basename.len] = 0;

		syms[1].st_name  = fb_buf_append_str(&strtab, fname);
		syms[1].st_info  = ELF64_ST_INFO(STB_LOCAL, STT_FILE);
		syms[1].st_other = 0;
		syms[1].st_shndx = SHN_ABS;
		syms[1].st_value = 0;
		syms[1].st_size  = 0;

		gb_free(heap_allocator(), fname);
	}

	// Count local vs global symbols for sh_info
	// ELF requires: all STB_LOCAL symbols come before STB_GLOBAL
	// We'll do two passes: first locals, then globals
	u32 local_count = 2; // null + file are local

	// First pass: count locals (non-exported, non-foreign procs)
	for_array(i, m->procs) {
		fbProc *p = m->procs[i];
		if (!p->is_foreign && !p->is_export) {
			local_count++;
		}
	}

	// Rebuild symbol table with proper ordering
	u32 actual_sym_count = 2 + cast(u32)m->procs.count;
	gb_free(heap_allocator(), syms);
	syms = gb_alloc_array(heap_allocator(), Elf64_Sym, actual_sym_count);
	gb_zero_size(syms, sizeof(Elf64_Sym) * actual_sym_count);

	// Re-add file symbol
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
		char *fname = gb_alloc_array(heap_allocator(), char, basename.len + 1);
		gb_memmove(fname, basename.text, basename.len);
		fname[basename.len] = 0;

		// Reset strtab — rebuild from scratch
		strtab.count = 0;
		fb_buf_append_byte(&strtab, 0);

		syms[1].st_name  = fb_buf_append_str(&strtab, fname);
		syms[1].st_info  = ELF64_ST_INFO(STB_LOCAL, STT_FILE);
		syms[1].st_other = 0;
		syms[1].st_shndx = SHN_ABS;
		syms[1].st_value = 0;
		syms[1].st_size  = 0;

		gb_free(heap_allocator(), fname);
	}

	// Second pass: add local procs, then global procs
	u32 sym_idx = 2;

	// Map from proc index to symbol index (for future relocation use)
	u32 *proc_sym_idx = gb_alloc_array(heap_allocator(), u32, m->procs.count);

	// Locals first (non-foreign, non-export)
	for_array(i, m->procs) {
		fbProc *p = m->procs[i];
		if (p->is_foreign || p->is_export) continue;

		char *name_cstr = gb_alloc_array(heap_allocator(), char, p->name.len + 1);
		gb_memmove(name_cstr, p->name.text, p->name.len);
		name_cstr[p->name.len] = 0;

		syms[sym_idx].st_name  = fb_buf_append_str(&strtab, name_cstr);
		syms[sym_idx].st_info  = ELF64_ST_INFO(STB_LOCAL, STT_FUNC);
		syms[sym_idx].st_other = 0;
		syms[sym_idx].st_shndx = FB_ELF_SEC_TEXT;
		syms[sym_idx].st_value = proc_text_offsets[i];
		syms[sym_idx].st_size  = p->machine_code_size;

		gb_free(heap_allocator(), name_cstr);
		proc_sym_idx[i] = sym_idx;
		sym_idx++;
	}

	// Then globals (exported + foreign)
	for_array(i, m->procs) {
		fbProc *p = m->procs[i];
		if (!p->is_foreign && !p->is_export) continue;

		char *name_cstr = gb_alloc_array(heap_allocator(), char, p->name.len + 1);
		gb_memmove(name_cstr, p->name.text, p->name.len);
		name_cstr[p->name.len] = 0;

		syms[sym_idx].st_name  = fb_buf_append_str(&strtab, name_cstr);
		syms[sym_idx].st_other = 0;

		if (p->is_foreign) {
			syms[sym_idx].st_info  = ELF64_ST_INFO(STB_GLOBAL, STT_NOTYPE);
			syms[sym_idx].st_shndx = SHN_UNDEF;
			syms[sym_idx].st_value = 0;
			syms[sym_idx].st_size  = 0;
		} else {
			syms[sym_idx].st_info  = ELF64_ST_INFO(STB_GLOBAL, STT_FUNC);
			syms[sym_idx].st_shndx = FB_ELF_SEC_TEXT;
			syms[sym_idx].st_value = proc_text_offsets[i];
			syms[sym_idx].st_size  = p->machine_code_size;
		}

		gb_free(heap_allocator(), name_cstr);
		proc_sym_idx[i] = sym_idx;
		sym_idx++;
	}

	actual_sym_count = sym_idx;

	// 4. Build .shstrtab (section name strings)
	fbBuf shstrtab = {};
	fb_buf_init(&shstrtab, 128);
	fb_buf_append_byte(&shstrtab, 0);
	u32 shname_text      = fb_buf_append_str(&shstrtab, ".text");
	u32 shname_symtab    = fb_buf_append_str(&shstrtab, ".symtab");
	u32 shname_strtab    = fb_buf_append_str(&shstrtab, ".strtab");
	u32 shname_shstrtab  = fb_buf_append_str(&shstrtab, ".shstrtab");
	u32 shname_relatext  = fb_buf_append_str(&shstrtab, ".rela.text");

	// 5. Calculate layout offsets
	u64 ehdr_size = sizeof(Elf64_Ehdr);

	u64 text_offset = ehdr_size;
	u64 text_size   = text_buf.count;

	// Align symtab to 8 bytes
	u64 symtab_offset = text_offset + text_size;
	if (symtab_offset % 8 != 0) symtab_offset += 8 - (symtab_offset % 8);
	u64 symtab_size = cast(u64)actual_sym_count * sizeof(Elf64_Sym);

	u64 strtab_offset = symtab_offset + symtab_size;
	u64 strtab_size   = strtab.count;

	u64 shstrtab_offset = strtab_offset + strtab_size;
	u64 shstrtab_size   = shstrtab.count;

	// .rela.text — empty for Phase 2
	u64 relatext_offset = shstrtab_offset + shstrtab_size;
	u64 relatext_size   = 0;

	// Section headers — align to 8
	u64 shdr_offset = relatext_offset + relatext_size;
	if (shdr_offset % 8 != 0) shdr_offset += 8 - (shdr_offset % 8);

	// 6. Build section headers
	Elf64_Shdr shdrs[FB_ELF_SEC_COUNT] = {};

	// Section 0: null
	// (already zeroed)

	// Section 1: .text
	shdrs[FB_ELF_SEC_TEXT].sh_name      = shname_text;
	shdrs[FB_ELF_SEC_TEXT].sh_type      = SHT_PROGBITS;
	shdrs[FB_ELF_SEC_TEXT].sh_flags     = SHF_ALLOC | SHF_EXECINSTR;
	shdrs[FB_ELF_SEC_TEXT].sh_offset    = text_offset;
	shdrs[FB_ELF_SEC_TEXT].sh_size      = text_size;
	shdrs[FB_ELF_SEC_TEXT].sh_addralign = 16;

	// Section 2: .symtab
	shdrs[FB_ELF_SEC_SYMTAB].sh_name      = shname_symtab;
	shdrs[FB_ELF_SEC_SYMTAB].sh_type      = SHT_SYMTAB;
	shdrs[FB_ELF_SEC_SYMTAB].sh_offset    = symtab_offset;
	shdrs[FB_ELF_SEC_SYMTAB].sh_size      = symtab_size;
	shdrs[FB_ELF_SEC_SYMTAB].sh_link      = FB_ELF_SEC_STRTAB; // associated string table
	shdrs[FB_ELF_SEC_SYMTAB].sh_info      = local_count;        // first non-local symbol index
	shdrs[FB_ELF_SEC_SYMTAB].sh_addralign = 8;
	shdrs[FB_ELF_SEC_SYMTAB].sh_entsize   = sizeof(Elf64_Sym);

	// Section 3: .strtab
	shdrs[FB_ELF_SEC_STRTAB].sh_name      = shname_strtab;
	shdrs[FB_ELF_SEC_STRTAB].sh_type      = SHT_STRTAB;
	shdrs[FB_ELF_SEC_STRTAB].sh_offset    = strtab_offset;
	shdrs[FB_ELF_SEC_STRTAB].sh_size      = strtab_size;
	shdrs[FB_ELF_SEC_STRTAB].sh_addralign = 1;

	// Section 4: .shstrtab
	shdrs[FB_ELF_SEC_SHSTRTAB].sh_name      = shname_shstrtab;
	shdrs[FB_ELF_SEC_SHSTRTAB].sh_type      = SHT_STRTAB;
	shdrs[FB_ELF_SEC_SHSTRTAB].sh_offset    = shstrtab_offset;
	shdrs[FB_ELF_SEC_SHSTRTAB].sh_size      = shstrtab_size;
	shdrs[FB_ELF_SEC_SHSTRTAB].sh_addralign = 1;

	// Section 5: .rela.text (empty for now)
	shdrs[FB_ELF_SEC_RELATEXT].sh_name      = shname_relatext;
	shdrs[FB_ELF_SEC_RELATEXT].sh_type      = SHT_RELA;
	shdrs[FB_ELF_SEC_RELATEXT].sh_offset    = relatext_offset;
	shdrs[FB_ELF_SEC_RELATEXT].sh_size      = relatext_size;
	shdrs[FB_ELF_SEC_RELATEXT].sh_link      = FB_ELF_SEC_SYMTAB;
	shdrs[FB_ELF_SEC_RELATEXT].sh_info      = FB_ELF_SEC_TEXT;
	shdrs[FB_ELF_SEC_RELATEXT].sh_addralign = 8;
	shdrs[FB_ELF_SEC_RELATEXT].sh_entsize   = sizeof(Elf64_Rela);

	// 7. Build ELF header
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
	ehdr.e_entry     = 0;
	ehdr.e_phoff     = 0;
	ehdr.e_shoff     = shdr_offset;
	ehdr.e_flags     = 0;
	ehdr.e_ehsize    = sizeof(Elf64_Ehdr);
	ehdr.e_phentsize = 0;
	ehdr.e_phnum     = 0;
	ehdr.e_shentsize = sizeof(Elf64_Shdr);
	ehdr.e_shnum     = FB_ELF_SEC_COUNT;
	ehdr.e_shstrndx  = FB_ELF_SEC_SHSTRTAB;

	// 8. Write to file
	String filepath = fb_filepath_obj(m);
	char *filepath_cstr = alloc_cstring(heap_allocator(), filepath);

	gbFile f = {};
	gbFileError ferr = gb_file_create(&f, filepath_cstr);
	if (ferr != gbFileError_None) {
		gb_printf_err("fast backend: failed to create object file '%s'\n", filepath_cstr);
		gb_free(heap_allocator(), filepath_cstr);
		fb_buf_free(&text_buf);
		fb_buf_free(&strtab);
		fb_buf_free(&shstrtab);
		gb_free(heap_allocator(), syms);
		gb_free(heap_allocator(), proc_text_offsets);
		gb_free(heap_allocator(), proc_sym_idx);
		return {};
	}

	// Write ELF header
	gb_file_write(&f, &ehdr, sizeof(ehdr));

	// Write .text
	if (text_buf.count > 0) {
		gb_file_write(&f, text_buf.data, text_buf.count);
	}

	// Pad to symtab alignment
	{
		u64 cur = ehdr_size + text_size;
		while (cur < symtab_offset) {
			u8 z = 0;
			gb_file_write(&f, &z, 1);
			cur++;
		}
	}

	// Write .symtab
	gb_file_write(&f, syms, sizeof(Elf64_Sym) * actual_sym_count);

	// Write .strtab
	gb_file_write(&f, strtab.data, strtab.count);

	// Write .shstrtab
	gb_file_write(&f, shstrtab.data, shstrtab.count);

	// .rela.text is empty, nothing to write

	// Pad to section header alignment
	{
		u64 cur = relatext_offset + relatext_size;
		while (cur < shdr_offset) {
			u8 z = 0;
			gb_file_write(&f, &z, 1);
			cur++;
		}
	}

	// Write section headers
	gb_file_write(&f, shdrs, sizeof(shdrs));

	gb_file_close(&f);

	// Cleanup
	gb_free(heap_allocator(), filepath_cstr);
	fb_buf_free(&text_buf);
	fb_buf_free(&strtab);
	fb_buf_free(&shstrtab);
	gb_free(heap_allocator(), syms);
	gb_free(heap_allocator(), proc_text_offsets);
	gb_free(heap_allocator(), proc_sym_idx);

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
