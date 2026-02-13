// Fast Backend IR — type definitions, opcode enum, instruction format
//
// This is the complete IR infrastructure for the fast backend.
// All types are self-contained; no LLVM or TB dependencies.

// Typed realloc helper: allocate new_count elements, copy old_count elements, zero remainder
#define gb_resize_array(allocator, ptr, old_count, new_count) \
	(decltype(ptr))gb_resize_align((allocator), (ptr), \
		(isize)(old_count) * gb_size_of(*(ptr)), \
		(isize)(new_count) * gb_size_of(*(ptr)), \
		gb_align_of(decltype(*(ptr))))

// Forward declarations
struct fbModule;
struct fbProc;
struct fbBuilder;

// ───────────────────────────────────────────────────────────────────────
// Type system (machine-level scalar types)
// ───────────────────────────────────────────────────────────────────────

// Machine-level scalar type system. Aggregates (structs, arrays, unions) are not
// representable here — they live in memory and are manipulated via pointer + load/store.
// For ABI register-pair decomposition (e.g., returning a struct in rax+rdx),
// fb_abi.cpp emits sequences of scalar loads/stores from a memory-backed slot.
enum fbTypeKind : u8 {
	FBT_VOID = 0,
	// I1 is a register-domain boolean type. In memory it occupies 1 byte.
	// The lowerer zero-extends on store and masks bit 0 on load.
	FBT_I1,
	FBT_I8,
	FBT_I16,
	FBT_I32,
	FBT_I64,
	FBT_I128,
	FBT_F16,
	FBT_F32,
	FBT_F64,
	FBT_PTR,

	FBT_COUNT,
};

struct fbType {
	fbTypeKind kind;
	u8         lanes; // 0 = scalar, 1..255 = SIMD lane count
};

#define FB_VOID       fbType{FBT_VOID, 0}
#define FB_I1         fbType{FBT_I1,   0}
#define FB_I8         fbType{FBT_I8,   0}
#define FB_I16        fbType{FBT_I16,  0}
#define FB_I32        fbType{FBT_I32,  0}
#define FB_I64        fbType{FBT_I64,  0}
#define FB_I128       fbType{FBT_I128, 0}
#define FB_F16        fbType{FBT_F16,  0}
#define FB_F32        fbType{FBT_F32,  0}
#define FB_F64        fbType{FBT_F64,  0}
#define FB_PTR        fbType{FBT_PTR,  0}
#define FB_VEC(k, n)  fbType{k, n}

gb_internal bool fb_type_eq(fbType a, fbType b) {
	return a.kind == b.kind && a.lanes == b.lanes;
}

// ───────────────────────────────────────────────────────────────────────
// Opcode enum (~102 opcodes)
// ───────────────────────────────────────────────────────────────────────

enum fbOp : u8 {
	// Constants & values
	FB_ICONST,
	FB_FCONST,
	FB_SYMADDR,
	FB_UNDEF,

	// Stack
	FB_ALLOCA,

	// Memory
	FB_LOAD,
	FB_STORE,
	FB_MEMCPY,
	FB_MEMSET,
	FB_MEMZERO,

	// Pointer arithmetic
	FB_MEMBER,
	FB_ARRAY,
	FB_PTR2INT,
	FB_INT2PTR,

	// Integer arithmetic
	FB_ADD,
	FB_SUB,
	FB_MUL,
	FB_SDIV,
	FB_UDIV,
	FB_SMOD,
	FB_UMOD,
	FB_NEG,

	// Bitwise
	FB_AND,
	FB_OR,
	FB_XOR,
	FB_NOT,
	FB_SHL,
	FB_LSHR,
	FB_ASHR,
	FB_ROL,
	FB_ROR,

	// Float arithmetic
	FB_FADD,
	FB_FSUB,
	FB_FMUL,
	FB_FDIV,
	FB_FNEG,
	FB_FABS,
	FB_SQRT,
	FB_FMIN,
	FB_FMAX,

	// Comparisons
	FB_CMP_EQ,
	FB_CMP_NE,
	FB_CMP_SLT,
	FB_CMP_SLE,
	FB_CMP_SGT,
	FB_CMP_SGE,
	FB_CMP_ULT,
	FB_CMP_ULE,
	FB_CMP_UGT,
	FB_CMP_UGE,
	FB_CMP_FEQ,
	FB_CMP_FNE,
	FB_CMP_FLT,
	FB_CMP_FLE,
	FB_CMP_FGT,
	FB_CMP_FGE,

	// Conversions
	FB_SEXT,
	FB_ZEXT,
	FB_TRUNC,
	FB_FPEXT,
	FB_FPTRUNC,
	FB_SI2FP,
	FB_UI2FP,
	FB_FP2SI,
	FB_FP2UI,
	FB_BITCAST,

	// Select
	FB_SELECT,

	// Control flow
	FB_JUMP,
	FB_BRANCH,
	FB_SWITCH,
	FB_RET,
	FB_UNREACHABLE,
	FB_TRAP,
	FB_DEBUGBREAK,

	// Function calls
	FB_CALL,
	FB_TAILCALL,

	// Atomics
	FB_ATOMIC_LOAD,
	FB_ATOMIC_STORE,
	FB_ATOMIC_XCHG,
	FB_ATOMIC_ADD,
	FB_ATOMIC_SUB,
	FB_ATOMIC_AND,
	FB_ATOMIC_OR,
	FB_ATOMIC_XOR,
	FB_ATOMIC_CAS,
	FB_FENCE,

	// Bit manipulation
	FB_BSWAP,
	FB_CLZ,
	FB_CTZ,
	FB_POPCNT,

	// Wide arithmetic
	FB_ADDPAIR,
	FB_MULPAIR,

	// Vector (SIMD)
	FB_VSHUFFLE,
	FB_VEXTRACT,
	FB_VINSERT,
	FB_VSPLAT,

	// Miscellaneous
	FB_VA_START,
	FB_PREFETCH,
	FB_CYCLE,
	FB_ASM,

	// SSA (future -O1)
	FB_PHI,

	FB_OP_COUNT,
};

// ───────────────────────────────────────────────────────────────────────
// Opcode operand role specification (used by verification and IR helpers)
// ───────────────────────────────────────────────────────────────────────

enum fbOperandRole : u8 {
	FBO_NONE,       // must be FB_NOREG
	FBO_VALUE,      // SSA value ID, must be < next_value
	FBO_VALUE_OPT,  // value ID or FB_NOREG (e.g., RET void)
	FBO_BLOCK,      // block ID, must be < block_count
	FBO_SLOT,       // slot index, must be < slot_count
	FBO_AUX,        // aux pool index, must be < aux_count
	FBO_COUNT,      // raw count (no range constraint)
};

struct fbOpSpec {
	fbOperandRole a, b, c;
	bool has_result;
	bool is_terminator;
};

// ───────────────────────────────────────────────────────────────────────
// Flag encodings
// ───────────────────────────────────────────────────────────────────────

// Memory operations (LOAD, STORE, atomic ops)
enum : u8 {
	FBF_VOLATILE = 1 << 0,
};

// Arithmetic (ADD, SUB, MUL, SHL)
enum : u8 {
	FBF_NSW = 1 << 0,
	FBF_NUW = 1 << 1,
};

// Atomic operations
enum : u8 {
	FBF_ORDER_MASK       = 0x07,
	FBF_FAIL_ORDER_SHIFT = 3,
};

// ───────────────────────────────────────────────────────────────────────
// Instruction format (32 bytes)
// ───────────────────────────────────────────────────────────────────────

enum : u32 { FB_NOREG = 0xFFFFFFFF };

// Abstract symbol index base for global variables.
// Abstract symbol index ranges:
//   [0, procs.count)                         — procedure symbols
//   [FB_RODATA_SYM_BASE, FB_RODATA_SYM_BASE + rodata.count) — rodata symbols
//   [FB_GLOBAL_SYM_BASE, FB_GLOBAL_SYM_BASE + globals.count) — global variable symbols
// Each range uses a stable base so that adding entries to one category
// does not shift indices in another.
enum : u32 { FB_RODATA_SYM_BASE = 0x20000000 };
enum : u32 { FB_GLOBAL_SYM_BASE = 0x40000000 };

struct fbInst {
	u8     op;       // fbOp
	u8     flags;    // per-opcode flags
	u16    type_raw; // fbType packed as (kind | lanes<<8)
	u32    r;        // result value ID (FB_NOREG if void)
	u32    a;        // operand 1
	u32    b;        // operand 2
	u32    c;        // operand 3
	u32    loc;      // index into fbProc::locs
	// Immediate / auxiliary value. 8 bytes keeps the struct at a power-of-two (32B)
	// and eliminates indirection for constants. A sidecar table would save space per
	// instruction at the cost of an extra pointer chase on every constant access.
	i64    imm;
};
static_assert(sizeof(fbInst) == 32, "instruction must be exactly 32 bytes");

gb_internal u16 fb_type_pack(fbType t) {
	return cast(u16)t.kind | (cast(u16)t.lanes << 8);
}

gb_internal fbType fb_type_unpack(u16 raw) {
	fbType t;
	t.kind  = cast(fbTypeKind)(raw & 0xFF);
	t.lanes = cast(u8)(raw >> 8);
	return t;
}

// ───────────────────────────────────────────────────────────────────────
// Relocations
// ───────────────────────────────────────────────────────────────────────

enum fbRelocType : u32 {
	FB_RELOC_ABS64 = 1,   // R_X86_64_64 (absolute 64-bit address)
	FB_RELOC_PC32  = 2,   // R_X86_64_PC32
	FB_RELOC_PLT32 = 4,   // R_X86_64_PLT32
};

struct fbReloc {
	u32         code_offset;   // byte offset in this proc's machine code
	u32         target_sym;    // abstract symbol index (proc, FB_RODATA_SYM_BASE+idx, or FB_GLOBAL_SYM_BASE+idx)
	i64         addend;        // typically -4
	fbRelocType reloc_type;
};

// Data relocation: a pointer fixup within a global variable's init_data.
// During ELF emission, the actual .data offset = global_data_offsets[global_idx] + local_offset.
struct fbDataReloc {
	u32 global_idx;    // index into global_entries
	u32 local_offset;  // byte offset within that global's init_data
	u32 target_sym;    // abstract symbol index (same scheme as text relocs)
	i64 addend;
};

// ───────────────────────────────────────────────────────────────────────
// Block
// ───────────────────────────────────────────────────────────────────────

struct fbBlock {
	u32 first_inst;
	u32 inst_count;
};

// ───────────────────────────────────────────────────────────────────────
// Stack slot
// ───────────────────────────────────────────────────────────────────────

struct fbStackSlot {
	u32     size;
	u32     align;
	i32     frame_offset; // assigned during lowering
	Entity *entity;       // NULL for temporaries
	Type   *odin_type;
	u32     scope_start;  // first instruction index where slot is live
	bool    is_indirect;  // true for MEMORY-class ABI params (slot holds pointer to caller data)
};

// ───────────────────────────────────────────────────────────────────────
// Source location
// ───────────────────────────────────────────────────────────────────────

enum : u16 {
	FBL_IS_STMT = 1 << 0,
};

struct fbLoc {
	u32 file_id;
	u32 line;
	u16 column;
	u16 flags;
};

// ───────────────────────────────────────────────────────────────────────
// Procedure
// ───────────────────────────────────────────────────────────────────────

struct fbProc {
	Entity *entity;
	Type   *odin_type;
	String  name;

	// IR storage (contiguous arrays)
	fbInst     *insts;
	u32         inst_count;
	u32         inst_cap;

	fbBlock    *blocks;
	u32         block_count;
	u32         block_cap;

	fbStackSlot *slots;
	u32          slot_count;
	u32          slot_cap;

	// Auxiliary operand pool (CALL args, SWITCH cases, RET values, PHI operands)
	u32 *aux;
	u32  aux_count;
	u32  aux_cap;

	// Source location table
	fbLoc *locs;
	u32    loc_count;
	u32    loc_cap;

	// SSA value counter
	u32 next_value;

	// Current block during IR construction
	u32 current_block;

	// Relocations (populated by lowering, consumed by ELF emission)
	fbReloc *relocs;
	u32      reloc_count;
	u32      reloc_cap;

	// Parameter ABI: param_locs[i] maps the i-th GP register argument to a stack
	// slot and sub-offset. Two-eightbyte params (string, slice) share one 16-byte
	// slot across two consecutive entries (sub_offset 0 and 8).
	struct fbParamLoc {
		u32 slot_idx;
		i32 sub_offset; // 0 for first/only eightbyte, 8 for second
	};
	fbParamLoc *param_locs;
	u32         param_count;

	// Multi-return: split return hidden output pointer params (Odin CC).
	// param_locs[split_returns_index + i] is the i-th output pointer param.
	// -1 means no split returns.
	i32         split_returns_index;
	i32         split_returns_count;
	// Split return parameter slots in call order (length == split_returns_count).
	// Each slot holds a pointer to the caller-provided output buffer for that return.
	u32        *split_return_slot_idxs;
	u32         split_return_slot_count;

	// Single MEMORY-class return: hidden output pointer parameter slot.
	// The callee receives the caller's output buffer address. -1 if no sret.
	i32         sret_slot_idx;

	// Odin CC: hidden context pointer parameter slot. -1 if none/unknown.
	i32         context_slot_idx;

	// XMM parameter ABI (non-Odin CC / foreign calls only).
	// Maps incoming XMM register arguments to stack slots for SSE-classified params.
	struct fbXmmParamLoc {
		u32 slot_idx;
		u8  xmm_idx;     // 0-7
		u8  float_kind;   // FBT_F32 or FBT_F64
	};
	fbXmmParamLoc *xmm_param_locs;
	u32             xmm_param_count;

	// Stack-passed parameter ABI (callee side).
	// When GP registers overflow (>6 eightbytes), overflow params arrive on the
	// caller's stack frame. Each entry maps a caller stack offset to a local slot.
	struct fbStackParamLoc {
		u32 slot_idx;
		i32 sub_offset;       // 0 for first eightbyte, 8 for second
		i32 caller_offset;    // byte offset from [RBP + 16]
	};
	fbStackParamLoc *stack_param_locs;
	u32              stack_param_count;

	// Parameter entity lookup: maps parameter Entity* → stack slot index.
	// Built during fb_setup_params, consumed during parameter binding to
	// avoid O(params * locs) linear search across param/xmm/stack arrays.
	struct fbParamEntityLoc {
		Entity *entity;
		u32     slot_idx;
	};
	fbParamEntityLoc *param_entity_locs;
	u32               param_entity_count;

	// Machine code output (populated by lowering)
	u8    *machine_code;
	u32    machine_code_size;
	bool   is_foreign;
	bool   is_export;
};

// ───────────────────────────────────────────────────────────────────────
// Target
// ───────────────────────────────────────────────────────────────────────

enum fbArch : u8 {
	FB_ARCH_X64,
	FB_ARCH_ARM64,
	FB_ARCH_UNKNOWN,
};

enum fbOS : u8 {
	FB_OS_LINUX,
	FB_OS_WINDOWS,
	FB_OS_MACOS,
	FB_OS_FREEBSD,
	FB_OS_UNKNOWN,
};

struct fbTarget {
	fbArch arch;
	fbOS   os;
	u8     ptr_size;
	u8     int_size;
	u64    features;
};

// ───────────────────────────────────────────────────────────────────────
// Source file registry
// ───────────────────────────────────────────────────────────────────────

struct fbSourceFile {
	String path;
	u32    id;
};

// ───────────────────────────────────────────────────────────────────────
// Symbols
// ───────────────────────────────────────────────────────────────────────

enum fbSymKind : u8 {
	FB_SYM_PROC,
	FB_SYM_GLOBAL,
	FB_SYM_EXTERNAL,
};

struct fbSymbol {
	fbSymKind kind;
	String    name;
	Entity   *entity;
	Type     *odin_type;

	// For FB_SYM_GLOBAL: initializer data
	u8       *init_data;   // NULL if zero-initialized (.bss)
	u32       init_size;
	u32       align;
	bool      is_tls;
	bool      is_read_only;

	// For FB_SYM_PROC: pointer to lowered machine code
	fbProc   *proc;
};

// ───────────────────────────────────────────────────────────────────────
// Module
// ───────────────────────────────────────────────────────────────────────

// Read-only data entry (string literals, constant arrays, etc.)
// Each entry is a blob of bytes placed in .rodata with a unique symbol.
struct fbRodataEntry {
	u8    *data;
	u32    size;
	String name;   // symbol name (e.g. ".L.str.0")
};

// Global variable entry (package-level variables).
// Each entry becomes a symbol in .data (constant-initialized) or .bss (zero-initialized).
// Abstract symbol index = FB_GLOBAL_SYM_BASE + global_entries index.
struct fbGlobalEntry {
	Entity *entity;
	String  name;
	Type   *odin_type;
	u8     *init_data;   // NULL → zero-init (.bss)
	u32     size;
	u32     align;
	bool    is_foreign;
	bool    is_export;
};

struct fbModule {
	Checker     *checker;
	CheckerInfo *info;
	LinkerData  *linker_data;
	fbTarget     target;

	Array<fbProc *>   procs;
	BlockingMutex     procs_mutex;

	Array<fbSymbol>   symbols;
	StringMap<u32>    symbol_map;
	BlockingMutex     symbols_mutex;

	// Read-only data (string literals, etc.)
	// Abstract symbol index for rodata entry i = FB_RODATA_SYM_BASE + i.
	Array<fbRodataEntry>  rodata_entries;
	StringMap<u32>        string_intern_map;  // string content → rodata entry index

	// Global variables (package-level).
	// Abstract symbol index for global entry i = FB_GLOBAL_SYM_BASE + i.
	Array<fbGlobalEntry>      global_entries;
	PtrMap<Entity *, u32>     global_entity_map;  // Entity* → global_entries index

	// Data relocations: pointer fixups within .data section global init_data.
	Array<fbDataReloc>        data_relocs;

	Array<fbSourceFile>        source_files;
	PtrMap<uintptr, u32>       file_id_to_idx;

	// Entry-point: proc indices for startup and user main (FB_NOREG if absent)
	u32 startup_proc_idx;
	u32 entry_proc_idx;

	// Type info globals (RTTI) — populated in a future phase
	fbSymbol *type_info_data;
	fbSymbol *type_info_types;
	fbSymbol *type_info_names;
	fbSymbol *type_info_offsets;
	fbSymbol *type_info_usings;
	fbSymbol *type_info_tags;

	// Map support: cached Map_Cell_Info and Map_Info global indices per type.
	PtrMap<Type *, u32>  map_cell_info_map;   // type → global_entries index
	PtrMap<Type *, u32>  map_info_map;        // map type → global_entries index
	PtrMap<Type *, u32>  map_hasher_procs;    // key type → procs index
	PtrMap<Type *, u32>  map_equal_procs;     // key type → procs index
};

// ───────────────────────────────────────────────────────────────────────
// Builder value (SSA value reference, 16 bytes, by-value)
// ───────────────────────────────────────────────────────────────────────

struct fbValue {
	u32   id;
	Type *type;
};

// ───────────────────────────────────────────────────────────────────────
// Address kinds (mirrors cgAddr pattern)
// ───────────────────────────────────────────────────────────────────────

enum fbAddrKind : u8 {
	fbAddr_Default,
	fbAddr_Map,
	fbAddr_Context,
	fbAddr_SOA,
	fbAddr_RelativePtr,
	fbAddr_RelativeSlice,
	fbAddr_Swizzle,
	fbAddr_SwizzleLarge,
	fbAddr_BitField,
};

struct fbAddr {
	fbAddrKind kind;
	fbValue    base;
	Type      *type;

	union {
		struct { fbValue key; Type *map_type; Type *result_type; } map;
		struct { Selection sel; } ctx;
		struct { fbValue index; Ast *index_expr; } soa;
		struct { bool deref; } relative;
		struct { u8 count; u8 indices[4]; } swizzle;
		struct { Slice<i32> indices; } swizzle_large;
		struct { u32 bit_offset; u32 bit_count; } bitfield;
	};
};

// ───────────────────────────────────────────────────────────────────────
// Calling conventions
// ───────────────────────────────────────────────────────────────────────

enum fbCallingConv : u8 {
	FBCC_ODIN     = 0,
	FBCC_C        = 1,
	FBCC_STDCALL  = 2,
	FBCC_FASTCALL = 3,
};

// ───────────────────────────────────────────────────────────────────────
// Defer
// ───────────────────────────────────────────────────────────────────────

enum fbDeferExitKind : u8 {
	fbDeferExit_Default,
	fbDeferExit_Return,
	fbDeferExit_Branch,
};

enum fbDeferKind : u8 {
	fbDefer_Node,
	fbDefer_Proc,
};

struct fbDefer {
	fbDeferKind kind;
	i32         scope_index;
	u32         block;
	union {
		Ast *stmt;                          // fbDefer_Node
		struct {                            // fbDefer_Proc
			fbValue   deferred;             // procedure symbol to call
			fbValue  *args;                 // captured argument values
			i32       arg_count;            // number of arguments
			TokenPos  pos;                  // source position for diagnostics
		} proc;
	};
};

// ───────────────────────────────────────────────────────────────────────
// Context data (implicit context parameter tracking)
// ───────────────────────────────────────────────────────────────────────

struct fbContextData {
	fbAddr ctx;
	bool   uses_default;
};

// ───────────────────────────────────────────────────────────────────────
// Target list (break/continue/fallthrough targets)
// ───────────────────────────────────────────────────────────────────────

struct fbTargetList {
	fbTargetList *prev;
	u32           break_block;
	u32           continue_block;
	u32           fallthrough_block;
	i32           scope_index;
	bool          is_block;
};

// ───────────────────────────────────────────────────────────────────────
// Branch regions
// ───────────────────────────────────────────────────────────────────────

struct fbBranchRegions {
	Ast *cond;
	u32  true_block;
	u32  false_block;
};

// ───────────────────────────────────────────────────────────────────────
// Switch case (for builder API)
// ───────────────────────────────────────────────────────────────────────

struct fbSwitchCase {
	i64 value;
	u32 block;
};

// ───────────────────────────────────────────────────────────────────────
// Builder state
// ───────────────────────────────────────────────────────────────────────

struct fbBuilder {
	fbProc   *proc;
	fbModule *module;

	// Current insertion point
	u32 current_block;
	u32 current_loc;

	// Odin entity
	Entity *entity;
	Type   *type;
	Ast    *body;
	DeclInfo *decl;

	// Scoping & control flow
	i32                     scope_index;
	Array<Scope *>          scope_stack;
	Array<fbContextData>    context_stack;
	Array<fbDefer>          defer_stack;
	fbTargetList           *target_list;
	Array<fbBranchRegions>  branch_regions;

	// Variable → address mapping
	PtrMap<Entity *, fbAddr>  variable_map;
	PtrMap<Entity *, fbAddr>  soa_values_map;

	// Procedure flags
	bool return_by_ptr;
	bool is_foreign;
	bool is_export;
	bool is_entry_point;
};

// ───────────────────────────────────────────────────────────────────────
// x86-64 register enum (hardware encoding)
// ───────────────────────────────────────────────────────────────────────

enum fbX64Reg : u8 {
	FB_RAX = 0,  FB_RCX = 1,  FB_RDX = 2,  FB_RBX = 3,
	FB_RSP = 4,  FB_RBP = 5,  FB_RSI = 6,  FB_RDI = 7,
	FB_R8  = 8,  FB_R9  = 9,  FB_R10 = 10, FB_R11 = 11,
	FB_R12 = 12, FB_R13 = 13, FB_R14 = 14, FB_R15 = 15,
	FB_X64_REG_NONE = 0xFF,
};

// SysV AMD64 ABI: max integer/pointer argument registers
enum : u32 { FB_X64_SYSV_MAX_GP_ARGS = 6 };

// ───────────────────────────────────────────────────────────────────────
// Register allocator state
// ───────────────────────────────────────────────────────────────────────

struct fbRegState {
	u32  vreg;      // IR value in this register (FB_NOREG if free)
	u32  last_use;  // instruction index of last use (for LRU eviction)
	bool dirty;     // modified since last spill?
};

struct fbStackLayout {
	u32 total_frame_size;  // total bytes subtracted from RSP (16-aligned)
	u32 slot_area_size;    // bytes used by stack slots
};

// Location of an IR value: positive = GP register index, negative = spilled
enum : i32 { FB_LOC_NONE = INT32_MIN };

// ───────────────────────────────────────────────────────────────────────
// Branch fixup (for forward jumps/branches)
// ───────────────────────────────────────────────────────────────────────

struct fbFixup {
	u32 code_offset;    // where the rel32 displacement is in the code buffer
	u32 target_block;   // which block it branches to
};

// ───────────────────────────────────────────────────────────────────────
// Lowering context (shared between x64/arm64)
// ───────────────────────────────────────────────────────────────────────

struct fbLowCtx {
	fbProc   *proc;
	fbModule *module;
	u8       *code;
	u32       code_count;
	u32       code_cap;
	u32      *block_offsets;

	// x86-64 register file
	fbRegState gp[16];

	// Value tracking: indexed by IR value ID
	i32 *value_loc;       // FB_LOC_NONE, or GP register index, or spill slot index (negative)
	u32  value_loc_count;

	// Current instruction index (for LRU tracking)
	u32 current_inst_idx;

	// Branch fixups (forward jumps patched after all blocks are emitted)
	fbFixup *fixups;
	u32      fixup_count;
	u32      fixup_cap;

	// Call relocations (accumulated during lowering, copied to fbProc)
	fbReloc *relocs;
	u32      reloc_count;
	u32      reloc_cap;

	// Symbol references: value_sym[vreg] = abstract symbol index when vreg is a SYMADDR.
	// FB_NOREG means the vreg is not a symbol reference.
	u32     *value_sym;

	// Stack frame layout
	fbStackLayout frame;
};

// ───────────────────────────────────────────────────────────────────────
// Forward declarations of fb_* functions
// ───────────────────────────────────────────────────────────────────────

gb_internal fbType fb_data_type(Type *t);
gb_internal i32    fb_type_size(fbType t);
gb_internal i32    fb_type_align(fbType t);
gb_internal bool   fb_type_is_float(fbType t);
gb_internal bool   fb_type_is_integer(fbType t);

gb_internal fbModule *fb_module_create(Checker *c);
gb_internal void      fb_module_destroy(fbModule *m);
gb_internal bool      fb_generate_code(Checker *c, LinkerData *ld);

gb_internal fbProc *fb_proc_create(fbModule *m, Entity *e);
gb_internal void    fb_proc_destroy(fbProc *p);
gb_internal u32     fb_block_create(fbProc *p);
gb_internal void    fb_block_start(fbProc *p, u32 block_id);
gb_internal u32     fb_inst_emit(fbProc *p, fbOp op, fbType type,
                                 u32 a, u32 b, u32 c, u32 loc, i64 imm);
gb_internal u32     fb_aux_push(fbProc *p, u32 val);
gb_internal u32     fb_slot_create(fbProc *p, u32 size, u32 align,
                                   Entity *entity, Type *odin_type);

gb_internal String  fb_get_entity_name(fbModule *m, Entity *e);
gb_internal String  fb_mangle_name(fbModule *m, Entity *e);
gb_internal String  fb_filepath_obj(fbModule *m);

gb_internal void    fb_generate_procedures(fbModule *m);
gb_internal void    fb_generate_globals(fbModule *m);
gb_internal void    fb_lower_proc_x64(fbLowCtx *ctx);
gb_internal void    fb_lower_all(fbModule *m);
gb_internal String  fb_emit_elf(fbModule *m);
gb_internal String  fb_emit_object(fbModule *m);

// AST walker (fb_build.cpp)
gb_internal fbValue fb_build_expr(fbBuilder *b, Ast *expr);
gb_internal fbAddr  fb_build_addr(fbBuilder *b, Ast *expr);
gb_internal void    fb_build_stmt(fbBuilder *b, Ast *node);
gb_internal void    fb_build_stmt_list(fbBuilder *b, Slice<Ast *> const &stmts);
gb_internal fbValue fb_addr_load(fbBuilder *b, fbAddr addr);
gb_internal void    fb_addr_store(fbBuilder *b, fbAddr addr, fbValue val);
gb_internal fbAddr  fb_add_local(fbBuilder *b, Type *type, Entity *entity, bool zero_init);
gb_internal fbValue fb_const_value(fbBuilder *b, Type *type, ExactValue value);
gb_internal fbValue fb_emit_conv(fbBuilder *b, fbValue val, Type *dst_type);

// Built-in procedures (fb_build_builtin.cpp)
gb_internal fbValue fb_build_builtin_proc(fbBuilder *b, Ast *expr,
                                          TypeAndValue const &tv, BuiltinProcId id);
