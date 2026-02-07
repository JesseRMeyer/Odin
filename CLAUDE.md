# Claude Code — Odin Compiler

## Build & test

```bash
make                  # debug build (clang++ src/main.cpp → ./odin)
make release          # -O3 build
./odin run examples/demo/demo.odin -file              # smoke test
./odin test tests/core/normal.odin -file -all-packages # core tests
./odin build <file> -fast -out:<name>                  # fast backend
bash tests/fast_backend/test_elf_symbols.sh            # fb tests
```

Single translation unit: `src/main.cpp` includes all `.cpp`. Requires LLVM 14/17-21, clang++.

## Compiler pipeline

```
tokenizer.cpp → parser.cpp → checker.cpp → [backend] → linker.cpp
```

Backend dispatch at `main.cpp:~4068`:
- `build_context.fast_backend` → `fb_generate_code()` (Linux/FreeBSD, `-fast` flag)
- `build_context.tilde_backend` → `cg_generate_code()` (Windows only)
- default → `llvm_backend_gen()` (all platforms)

## Source tree

```
src/                    # All compiler C++14 (monolithic build)
  main.cpp              # CLI, orchestration, includes everything
  common.cpp, gb/gb.h   # Utility library, custom allocators
  tokenizer.cpp         # Lexer
  parser.cpp/.hpp       # Recursive descent parser, AST definitions
  entity.cpp            # Entity (named declarations)
  types.cpp             # Type system
  checker.cpp/.hpp      # Type checker orchestration, Scope, CheckerContext
  check_expr.cpp        # Expression checking
  check_stmt.cpp        # Statement checking
  check_decl.cpp        # Declaration checking
  check_type.cpp        # Type checking
  check_builtin.cpp     # Builtin procedure checking
  build_settings.cpp    # Build flags, targets, microarch
  error.cpp             # Diagnostics
  linker.cpp            # System linker invocation

  # LLVM backend (lb_ prefix)
  llvm_backend.cpp      # Entry: lb_generate_code(), lbGenerator, lbModule
  llvm_backend_expr.cpp # lb_build_expr() → lbValue
  llvm_backend_stmt.cpp # lb_build_stmt()
  llvm_backend_proc.cpp # lb_create_procedure(), lb_begin/end_procedure_body()
  llvm_backend_type.cpp # lb_type() — Odin Type → LLVMTypeRef
  llvm_backend_utility.cpp
  llvm_backend_const.cpp
  llvm_backend_debug.cpp
  llvm_abi.cpp          # lbFunctionType, lbArgType (Direct/Indirect/Ignore)

  # Fast backend (fb_ prefix, ~7K lines)
  fb_ir.h               # IR types, opcodes, all structs
  fb_ir.cpp             # IR infrastructure
  fb_build.cpp          # AST → IR: fb_build_expr(), fb_build_stmt()
  fb_build_builtin.cpp  # Builtin procedure codegen
  fb_lower_x64.cpp      # IR → x86-64: fb_lower_proc_x64(), register allocator
  fb_emit_elf.cpp       # ELF .o writer: fb_emit_elf()
  fb_abi.cpp            # SysV ABI: fb_abi_classify_type_sysv()

  # Tilde backend (cg_ prefix, Windows only)
  tilde.cpp, tilde_expr.cpp, tilde_stmt.cpp, tilde_proc.cpp

base/runtime/           # Runtime library (Odin)
  core.odin             # Core runtime definitions
  core_builtin.odin     # Builtin type methods (append, delete, etc.)
  internal.odin         # Internal runtime procs
  entry_unix.odin       # Platform entry points
  heap_allocator.odin   # Memory management
  print.odin            # Printf implementation

core/                   # Standard library (38 packages, Odin)
  fmt/ strings/ os/ math/ crypto/ container/ sync/ net/ io/ encoding/ ...

vendor/                 # Third-party libs (glfw, opengl, sdl2, etc.)
tests/                  # Test suite (core/, fast_backend/, internal/, issues/)
```

## Core data structures (all in `src/`)

### AST — `parser.hpp`
```cpp
struct Ast {
    AstKind    kind;            // enum, 183 variants
    u8         state_flags;
    i32        file_id;
    TypeAndValue tav;           // type + value, populated by checker
    union { /* variant per kind */ };
};
// Key kinds: Ident, Literal, BinaryExpr, UnaryExpr, CallExpr, SelectorExpr,
//   IndexExpr, SliceExpr, TypeAssertion, CompoundLit,
//   BlockStmt, IfStmt, ForStmt, RangeStmt, SwitchStmt, ReturnStmt, DeferStmt,
//   AssignStmt, ValueDecl, ProcLit, ProcType, StructType, UnionType, EnumType
```

### Type — `types.cpp`
```cpp
struct Type {
    TypeKind kind;              // Basic, Named, Pointer, Array, Slice, DynamicArray, Map,
                                // Struct, Union, Enum, Tuple, Proc, BitSet, SimdVector, Matrix, ...
    union {
        TypeBasic    Basic;     // BasicKind: bool, i8-i128, u8-u128, f16/32/64, string, any, typeid
        TypePointer  Pointer;   // { Type *elem; }
        TypeArray    Array;     // { Type *elem; i64 count; }
        TypeSlice    Slice;     // { Type *elem; }
        TypeStruct   Struct;    // { Slice<Entity*> fields; i64 *offsets; bool is_packed,is_raw_union; }
        TypeUnion    Union;     // { variants + tag }
        TypeProc     Proc;      // { Type *params,*results; ProcCallingConvention cc; }
        TypeTuple    Tuple;     // { Slice<Entity*> variables; }
        // ...
    };
    atomic<i64> cached_size, cached_align;
};
```

### Entity — `entity.cpp`
```cpp
struct Entity {
    EntityKind  kind;           // Constant, Variable, TypeName, Procedure, ProcGroup,
                                // Builtin, ImportName, LibraryName, Nil, Label
    atomic<EntityState> state;  // Unresolved → InProgress → Resolved
    u64         flags;          // EntityFlag: Used, Field, Param, Result, Test, Init, ...
    Token       token;          // declaration location
    Scope      *scope;
    Type       *type;
    DeclInfo   *decl_info;
    AstFile    *file;
    AstPackage *pkg;
    union { /* per-kind: Constant{ExactValue}, Variable{link_name}, Procedure{tags,link_name}, ... */ };
};
```

### Scope — `checker.hpp`
```cpp
struct Scope {
    Scope  *parent;
    i32     flags;              // ScopeFlag: Pkg, File, Proc, Builtin, Global, Type
    StringMap<Entity*> elements; // symbol table
    PtrSet<Scope*> imported;
    union { AstPackage *pkg; AstFile *file; Entity *procedure_entity; };
};
```

### Checker — `checker.hpp`
```cpp
struct CheckerContext {          // per-thread checker state
    Checker     *checker;
    AstPackage  *pkg;
    AstFile     *file;
    Scope       *scope;
    DeclInfo    *decl;
    Type        *type_hint;
    DeclInfo    *curr_proc_decl;
    Type        *curr_proc_sig;
    // ...
};
struct CheckerInfo {            // global state
    StringMap<AstFile*>    files;
    StringMap<AstPackage*> packages;
    Entity *entry_point;
    Array<Entity*> entities;
    // type info caches, definition queues, ...
};
// Entry: check_parsed_files() in checker.cpp
// Expr:  check_expr(CheckerContext*, Operand*, Ast*) in check_expr.cpp
// Stmt:  check_stmt(CheckerContext*, Ast*, u32 flags) in check_stmt.cpp
```

### Data flow between phases
```
Ast (parser) → Entity + Type + Scope (checker) → lbValue/fbValue (backend)

Ast.Ident.entity     → Entity
Entity.type           → Type
Scope.elements[name]  → Entity
Ast.tav               → TypeAndValue {AddressingMode, Type*, ExactValue}
```

## LLVM backend structures

```cpp
struct lbValue { LLVMValueRef value; Type *type; };
struct lbAddr  { lbAddrKind kind; lbValue addr; /* union: map, ctx, soa, swizzle, bitfield */ };
struct lbModule {
    LLVMModuleRef mod; LLVMContextRef ctx;
    PtrMap<u64,LLVMTypeRef> types;
    PtrMap<Entity*,lbValue> values;
    StringMap<lbProcedure*> procedures;
};
struct lbProcedure {
    lbModule *module; Entity *entity; Type *type; Ast *body;
    LLVMValueRef value; LLVMBuilderRef builder;
    lbBlock *curr_block; lbAddr return_ptr;
    Array<lbDefer> defer_stmts;
};
// Key functions:
//   lb_generate_code(lbGenerator*)         — entry from main
//   lb_build_expr(lbProcedure*, Ast*)      → lbValue
//   lb_build_addr(lbProcedure*, Ast*)      → lbAddr
//   lb_build_stmt(lbProcedure*, Ast*)
//   lb_type(lbModule*, Type*)              → LLVMTypeRef
//   lb_emit_arith(p, op, lhs, rhs, type)  → lbValue
//   lb_emit_comp(p, op, left, right)       → lbValue
//   lb_addr_load(p, addr) / lb_addr_store(p, addr, val)
//   lb_emit_load(p, ptr) / lb_emit_store(p, ptr, val)
//   lb_create_block(p, name) / lb_emit_jump(p, blk) / lb_emit_cond(p, cond, t, f)
//   lb_add_local(p, type, entity, zero_init)
```

## Fast backend structures

### fbInst — 32 bytes, fixed-size IR instruction (`fb_ir.h`)
```cpp
struct fbInst {
    u8  op;         // fbOp enum
    u8  flags;      // NSW/NUW, volatile, etc
    u16 type_raw;   // fbTypeKind | (lanes << 8)
    u32 r;          // result value ID (FB_NOREG if void)
    u32 a, b, c;    // operand value IDs
    u32 loc;        // source location index
    i64 imm;        // immediate / offset / alignment
};
```

### fbType — scalar types
```cpp
enum fbTypeKind : u8 {
    FBT_VOID, FBT_I1, FBT_I8, FBT_I16, FBT_I32, FBT_I64, FBT_I128,
    FBT_F16, FBT_F32, FBT_F64, FBT_PTR
};
struct fbType { fbTypeKind kind; u8 lanes; }; // lanes=0 scalar, >0 SIMD
```

### Opcodes (fbOp) — 102 total
```
Constants:   FB_ICONST FB_FCONST FB_SYMADDR FB_UNDEF
Memory:      FB_ALLOCA FB_LOAD FB_STORE FB_MEMCPY FB_MEMSET FB_MEMZERO
Pointers:    FB_MEMBER(byte offset) FB_ARRAY(index*stride) FB_PTR2INT FB_INT2PTR
Int arith:   FB_ADD FB_SUB FB_MUL FB_SDIV FB_UDIV FB_SMOD FB_UMOD FB_NEG
Bitwise:     FB_AND FB_OR FB_XOR FB_NOT FB_SHL FB_LSHR FB_ASHR FB_ROL FB_ROR
Float:       FB_FADD FB_FSUB FB_FMUL FB_FDIV FB_FNEG FB_FABS FB_SQRT FB_FMIN FB_FMAX
Int cmp:     FB_CMP_EQ FB_CMP_NE FB_CMP_{S,U}{LT,LE,GT,GE}
Float cmp:   FB_CMP_F{EQ,NE,LT,LE,GT,GE}
Convert:     FB_SEXT FB_ZEXT FB_TRUNC FB_FPEXT FB_FPTRUNC FB_SI2FP FB_UI2FP FB_FP2SI FB_FP2UI FB_BITCAST
Control:     FB_JUMP FB_BRANCH FB_SWITCH FB_RET FB_UNREACHABLE FB_TRAP
Other:       FB_SELECT FB_CALL FB_TAILCALL FB_PROJ(multi-return) FB_PHI
Atomics:     FB_ATOMIC_{LOAD,STORE,XCHG,ADD,SUB,AND,OR,XOR,CAS} FB_FENCE
Bit ops:     FB_BSWAP FB_CLZ FB_CTZ FB_POPCNT
Vector:      FB_VSHUFFLE FB_VEXTRACT FB_VINSERT FB_VSPLAT
Misc:        FB_VA_START FB_PREFETCH FB_CYCLE FB_ASM
```

### fbProc, fbBlock, fbValue, fbAddr
```cpp
struct fbBlock { u32 first_inst; u32 inst_count; };
struct fbStackSlot { u32 size, align; i32 frame_offset; Entity *entity; Type *odin_type; };
struct fbProc {
    Entity *entity; Type *odin_type; String name;
    fbInst *insts;      u32 inst_count, inst_cap;    // contiguous instruction array
    fbBlock *blocks;    u32 block_count, block_cap;
    fbStackSlot *slots; u32 slot_count, slot_cap;
    u32 *aux;           u32 aux_count, aux_cap;       // call args, switch cases
    u32 next_value;                                    // SSA counter
    u32 current_block;                                 // insertion point
    fbParamLoc *param_locs; u32 param_count;           // ABI param layout
    i32 split_returns_index, split_returns_count;      // Odin CC multi-return
    fbReloc *relocs;    u32 reloc_count, reloc_cap;
    u8 *machine_code;   u32 machine_code_size;         // lowering output
    bool is_foreign, is_export;
};
struct fbValue { u32 id; Type *type; };                // SSA reference
struct fbAddr {
    fbAddrKind kind;    // Default, Map, Context, SOA, RelativePtr, Swizzle, BitField, ...
    fbValue base;       // pointer
    Type *type;
};
struct fbGlobalEntry {
    Entity *entity; String name; Type *odin_type;
    u8 *init_data;   // NULL → .bss, non-NULL → .data
    u32 size, align; bool is_foreign, is_export;
};
struct fbModule {
    Checker *checker; fbTarget target;
    Array<fbProc*> procs; Array<fbSymbol> symbols; StringMap<u32> symbol_map;
    Array<fbRodataEntry> rodata_entries; StringMap<u32> string_intern_map;
    Array<fbGlobalEntry> global_entries; PtrMap<Entity*, u32> global_entity_map;
};
```

### Builder — `fb_build.cpp`
```cpp
struct fbBuilder {
    fbProc *proc; fbModule *module;
    u32 current_block, current_loc;
    PtrMap<Entity*, fbAddr> variable_map;              // locals
    Array<fbDefer> defer_stack;
    fbTargetList *target_list;                         // break/continue targets
    bool return_by_ptr;
};
// Key functions:
//   fb_generate_code(Checker*, LinkerData*)   — entry from main.cpp
//   fb_generate_procedures(fbModule*)         — two-pass: create procs, then build IR
//   fb_generate_globals(fbModule*)            — discover & serialize package-level variables
//   fb_build_expr(fbBuilder*, Ast*)           → fbValue
//   fb_build_addr(fbBuilder*, Ast*)           → fbAddr
//   fb_build_stmt(fbBuilder*, Ast*)
//   fb_build_call_expr(fbBuilder*, Ast*)      → fbValue
//   fb_build_compound_lit(fbBuilder*, Ast*)   → fbAddr
//
// Emit helpers:
//   fb_emit(b, op, type, a, b, c, imm)       → fbValue  (raw instruction)
//   fb_emit_iconst(b, type, val)              → fbValue
//   fb_emit_fconst(b, type, val)              → fbValue
//   fb_emit_load(b, ptr, elem_type)           → fbValue
//   fb_emit_store(b, ptr, val)
//   fb_emit_arith(b, op, lhs, rhs, type)      → fbValue
//   fb_emit_cmp(b, cmp_op, lhs, rhs)          → fbValue
//   fb_emit_conv(b, val, dst_type)             → fbValue
//   fb_emit_member(b, base, byte_offset)       → fbValue (GEP-like)
//   fb_emit_array_access(b, base, idx, stride) → fbValue
//   fb_emit_symaddr(b, proc_idx)               → fbValue
//   fb_emit_memcpy(b, dst, src, size, align)
//   fb_emit_memzero(b, ptr, size, align)
//   fb_emit_jump(b, target_block)
//   fb_emit_branch(b, cond, true_blk, false_blk)
//   fb_emit_ret(b, val)
//   fb_emit_select(b, cond, t, f, type)        → fbValue
//   fb_new_block(b) / fb_set_block(b, id)
//   fb_add_local(b, type, entity, zero_init)   → fbAddr
//   fb_addr_load(b, addr) / fb_addr_store(b, addr, val)
//   fb_scope_open(b, scope) / fb_scope_close(b, kind, target_scope)
```

### Lowering — `fb_lower_x64.cpp`
```cpp
struct fbRegState { u32 vreg; u32 last_use; bool dirty; };
struct fbLowCtx {
    fbProc *proc; fbModule *module;
    u8 *code;          u32 code_count, code_cap;       // output machine code
    u32 *block_offsets;                                 // per-block code offset
    fbRegState gp[16];                                  // GP register state
    i32 *value_loc;    u32 value_loc_count;             // vreg → reg/spill loc
    fbFixup *fixups;   u32 fixup_count, fixup_cap;     // branch patches
    fbReloc *relocs;   u32 reloc_count, reloc_cap;     // call relocations
    fbStackLayout frame;
};
// Registers: FB_RAX=0..FB_R15=15, FB_X64_REG_NONE=0xFF, FB_XMM0=0..
// Key functions:
//   fb_lower_proc_x64(fbLowCtx*)                  — main dispatch loop over insts
//   fb_lower_all(fbModule*)                        — lower all procs
//   fb_x64_alloc_gp(ctx, vreg, exclude_mask)       → fbX64Reg (allocate register)
//   fb_x64_resolve_gp(ctx, vreg, exclude_mask)     → fbX64Reg (get or load from spill)
//   fb_x64_spill_reg(ctx, reg)                     — evict register to stack
//   fb_x64_find_lru(ctx, exclude_mask)             → fbX64Reg (LRU eviction)
//   fb_x64_emit_prologue/epilogue(ctx)
//   fb_x64_emit_jmp(ctx, target_block, current_bi)
//   fb_x64_emit_jcc(ctx, cc, target_block, current_bi)
//   fb_x64_record_fixup(ctx, code_offset, target_block)
//   fb_x64_record_reloc(ctx, code_offset, target_sym, addend, type)
// Encoding: fb_x64_rex(), fb_x64_modrm(), fb_x64_sib(), fb_x64_imm32/64()
// Patterns: fb_x64_alu_rr(), fb_x64_shift_cl(), fb_x64_div(), fb_x64_float_binop()
```

### ELF emission — `fb_emit_elf.cpp`
```cpp
// fb_emit_elf(fbModule*) → String (output path)
// Sections: NULL, .text, .rodata, .data, .bss, .symtab, .strtab, .shstrtab, .rela.text
// Process: concat proc machine code → build .rodata/.data/.bss → build symbols → build relocations → write file
// Abstract symbol index: [0,procs) procs, [procs,procs+rodata) rodata, [FB_GLOBAL_SYM_BASE,...) globals
// FB_GLOBAL_SYM_BASE = 0x40000000 — separates global indices from rodata (avoids count dependency)
// Reloc types: FB_RELOC_PC32 (R_X86_64_PC32), FB_RELOC_PLT32 (R_X86_64_PLT32)
// Helper: fbBuf { u8 *data; u32 count, cap; } with fb_buf_append/align/free
```

### ABI — `fb_abi.cpp`
```cpp
enum fbABIClass : u8 { FB_ABI_INTEGER, FB_ABI_SSE, FB_ABI_MEMORY, FB_ABI_IGNORE };
struct fbABIParamInfo { fbABIClass classes[2]; u8 num_classes; Type *odin_type; };
// fb_abi_classify_type_sysv(Type*) → fbABIParamInfo
// INTEGER: all ints, ptrs, enums, bitsets; string/any/slice → INTEGER×2
// SSE: f16, f32, f64 (currently routed through GP in intra-backend calls)
// MEMORY: complex, quaternion, dynamic arrays, maps, aggregates (conservative)
// SysV arg regs: RDI, RSI, RDX, RCX, R8, R9 (6 max GP args)
```

## Naming conventions

- `fb_` fast backend, `lb_` LLVM backend, `cg_` tilde backend, `check_` checker
- Snake_case functions/variables, PascalCase types/structs
- IR types: `fbInst`, `fbBlock`, `fbProc`, `fbType`, `fbValue`, `fbAddr`
- Memory: per-procedure arenas, freed after emission

## Testing as independent validation

Write tests as a separate derivation from the spec, not from the implementation. The test encodes "what should happen" and the code encodes "how it happens" — two independent artifacts that validate each other. When both agree, confidence is multiplicative. When they disagree, one of them is wrong, and that's the signal.

Concretely: write the test from the language semantics / expected behavior *before* looking at how the implementation achieves it. Don't mirror implementation structure in tests. A test that's just a transliteration of the code it tests catches nothing.

## Code generation rules

**No iterative drafts.** Never write code that builds, fails, tears down, rebuilds within the same function. Discard and rewrite cleanly. Final code = only the working solution.

**Plan control flow before emitting.** For code with multiple basic blocks, phi nodes, or shared exits: work out full block structure and dataflow before writing any code.

**Clean code only.** No dead code paths, abandoned attempts, or stream-of-consciousness comments in committed code.

## Workflow

1. Use task list (TaskCreate) to plan multi-step work at session start
2. Break into small, compilable increments
3. Build (`make`) after each change to catch regressions
4. Commit after each completed task
5. If session ends early, summarize remaining work in commit message
6. **Keep this file accurate.** When adding/removing/renaming files, structs, key functions, or opcodes, update the relevant sections of this CLAUDE.md in the same commit. A stale map is worse than no map.

## Commit style

`<area>: <description>` — e.g.:
- `fast backend: add multi-return support and range statements`
- `fast backend: fix shift spill, any ABI, bool conversion ordering`
