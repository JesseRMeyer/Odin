# Fast Backend (`fb_`) — Linear SSA IR for Odin Debug Builds

## 1. Design Goals

1. **Maximum compilation speed.** Two linear passes: AST → IR, IR → machine code. No graph structures, no iterative algorithms, no scheduling.
2. **Decent -O0 codegen.** Expressions compute in registers. Variables live on the stack for debugger visibility. Block-local register allocation keeps memory traffic low.
3. **Full Odin semantics.** Every language feature is supported. Complex addressing (maps, SOA, swizzle, relative pointers, bit fields) is resolved in the builder layer, not the IR.
4. **SSA-ready.** The IR is in SSA form. At -O0, mutable variables use alloca+load/store (no phi nodes needed). A future -O1 path adds mem2reg + peephole passes using the same IR.
5. **Data-oriented.** Fixed-size instructions in contiguous arrays. Arena allocation. Indices instead of pointers. Cache-friendly iteration.
6. **Dual-target.** x86-64 and ARM64 from the start. Target-specific details are confined to the lowering layer.

## 2. Architecture

```
                    ┌─────────────────┐
   Odin AST ───────►  fb_build_*()   │  Pass 1: AST → IR
   (checked)        │  (builder layer)│  One forward pass over AST.
                    │                 │  Resolves Odin semantics to
                    │  Produces:      │  primitive IR operations.
                    │  fbInst[]       │
                    │  fbBlock[]      │
                    │  fbStackSlot[]  │
                    └────────┬────────┘
                             │  fbProc (flat arrays)
                    ┌────────▼────────┐
                    │  fb_lower_*()   │  Pass 2: IR → machine code
                    │  (x64 or arm64) │  One forward pass per block.
                    │                 │  Block-local register allocation.
                    │  Produces:      │  Direct binary encoding.
                    │  machine code   │
                    │  relocations    │
                    │  debug info     │
                    └────────┬────────┘
                             │
                    ┌────────▼────────┐
                    │  fb_emit_*()    │  Object file emission
                    │  (elf/pe/macho) │  + DWARF / CodeView
                    └────────┬────────┘
                             │
                        .o / .obj
                             │
                    ┌────────▼────────┐
                    │  linker_stage() │  Existing Odin linker
                    └─────────────────┘
```

The IR exists only transiently — built for one procedure, lowered, then freed. No whole-program IR is ever materialized. Each procedure's arena is released after its machine code is emitted.

## 3. Type System

The IR uses machine-level scalar types. Odin `Type*` pointers are carried alongside for debug info and ABI decisions but do not appear in instructions.

```cpp
enum fbTypeKind : u8 {
    FBT_VOID = 0,    // no value (for stores, branches, etc.)
    FBT_I1,          // boolean
    FBT_I8,
    FBT_I16,
    FBT_I32,
    FBT_I64,
    FBT_I128,
    FBT_F16,
    FBT_F32,
    FBT_F64,
    FBT_PTR,         // pointer (target-width)

    FBT_COUNT,
};

// Packed 16-bit type descriptor.
// Scalar: lanes == 0. SIMD vector: lanes == 2,4,8,16,32,64.
struct fbType {
    fbTypeKind kind;
    u8         lanes;  // 0 = scalar
};

// Convenience constructors.
#define FB_VOID    fbType{FBT_VOID, 0}
#define FB_I1      fbType{FBT_I1,   0}
#define FB_I8      fbType{FBT_I8,   0}
#define FB_I16     fbType{FBT_I16,  0}
#define FB_I32     fbType{FBT_I32,  0}
#define FB_I64     fbType{FBT_I64,  0}
#define FB_I128    fbType{FBT_I128, 0}
#define FB_F16     fbType{FBT_F16,  0}
#define FB_F32     fbType{FBT_F32,  0}
#define FB_F64     fbType{FBT_F64,  0}
#define FB_PTR     fbType{FBT_PTR,  0}
#define FB_VEC(k, n)  fbType{k, n}    // e.g. FB_VEC(FBT_F32, 4) for #simd[4]f32
```

**No aggregate types.** Structs, arrays, slices, strings, unions, dynamic arrays, and maps exist only in memory. The IR accesses their fields via pointer arithmetic (`MEMBER`, `ARRAY`) and `LOAD`/`STORE`. This keeps the instruction set small and the lowering trivial.

**SIMD alignment:** For vector types (`lanes > 0`), alignment is the total vector size rounded up to the next power of two, capped at `build_context.max_simd_align`. This avoids non-power-of-two alignments (e.g., a 3-lane i32 vector has size 12 but alignment 16).

Odin `Type*` is carried in `fbValue` and `fbStackSlot` for:
- ABI lowering (struct passing/returning conventions)
- Debug info (DWARF type DIEs)
- The builder layer's own bookkeeping (type-checking IR construction)

## 4. Instruction Format

Every instruction is **32 bytes**, enabling O(1) indexing and predictable cache behavior (2 instructions per 64-byte cache line).

```cpp
enum : u32 { FB_NOREG = 0xFFFFFFFF };

struct fbInst {
    u8     op;       // offset 0:  fbOp enum
    u8     flags;    // offset 1:  per-opcode flags (see §4.1)
    u16    type_raw; // offset 2:  fbType packed as (kind | lanes<<8)
    u32    r;        // offset 4:  result value ID (FB_NOREG if void)
    u32    a;        // offset 8:  operand 1 (value ID, block ID, or slot index)
    u32    b;        // offset 12: operand 2
    u32    c;        // offset 16: operand 3
    u32    loc;      // offset 20: index into procedure's location table
    i64    imm;      // offset 24: immediate value / auxiliary index (8-byte aligned)
};
static_assert(sizeof(fbInst) == 32, "instruction must be exactly 32 bytes");
```

**Field semantics vary by opcode** (documented per-opcode in §5). The naming convention:
- `r` — result (the defined value)
- `a, b, c` — source operands (value IDs referencing earlier definitions)
- `imm` — compile-time constant: integer literal, float bits, byte offset, or packed auxiliary index
- `loc` — index into `fbProc::locs[]`, encoding source file + line + column
- `flags` — opcode-specific bits (volatile, memory order, signedness, etc.)

### 4.1 Flag Encodings

```cpp
// Memory operations (LOAD, STORE, atomic ops)
enum : u8 {
    FBF_VOLATILE  = 1 << 0,
};

// Arithmetic (ADD, SUB, MUL, SHL)
enum : u8 {
    FBF_NSW = 1 << 0,   // no signed wrap (for future overflow checks)
    FBF_NUW = 1 << 1,   // no unsigned wrap
};

// Atomic operations
// flags[2:0] = memory order (0=relaxed..5=seq_cst)
// flags[5:3] = failure order (for CAS only)
enum : u8 {
    FBF_ORDER_MASK      = 0x07,
    FBF_FAIL_ORDER_SHIFT = 3,
};
```

## 5. Opcode Reference

Each row documents one opcode's use of the instruction fields.
`-` means the field is unused for that opcode.

### 5.1 Constants & Values

| Op | r | a | b | c | imm | flags | Description |
|----|---|---|---|---|-----|-------|-------------|
| `ICONST` | dst | - | - | - | value (i64) | - | Integer/bool constant |
| `FCONST` | dst | - | - | - | bits (u64 of f32/f64) | - | Float constant (bit-punned) |
| `SYMADDR` | dst | - | - | - | symbol index | - | Address of global/function |
| `UNDEF` | dst | - | - | - | - | - | Undefined value (for uninitialized) |

### 5.2 Stack

| Op | r | a | b | c | imm | flags | Description |
|----|---|---|---|---|-----|-------|-------------|
| `ALLOCA` | dst (ptr) | - | - | - | size\|align<<32 | - | Allocate stack slot, returns pointer |

`imm` packs both size (low 32) and alignment (high 32). The builder helper unpacks.

### 5.3 Memory

| Op | r | a | b | c | imm | flags | Description |
|----|---|---|---|---|-----|-------|-------------|
| `LOAD` | dst | ptr | - | - | align | volatile | Load from memory |
| `STORE` | - | ptr | val | - | align | volatile | Store to memory |
| `MEMCPY` | - | dst | src | size | align | - | Bulk memory copy |
| `MEMSET` | - | dst | val(i8) | size | align | - | Bulk memory fill |
| `MEMZERO` | - | dst | size | - | align | - | Zero memory |

For `MEMCPY`/`MEMSET`/`MEMZERO`, `size` is a value ID (dynamic size). For statically known sizes, the builder can emit a constant value.

### 5.4 Pointer Arithmetic

| Op | r | a | b | c | imm | flags | Description |
|----|---|---|---|---|-----|-------|-------------|
| `MEMBER` | dst | base | - | - | byte offset (i64) | - | `base + const_offset` |
| `ARRAY` | dst | base | index | - | stride (i64) | - | `base + index * stride` |
| `PTR2INT` | dst | ptr | - | - | - | - | Pointer to integer |
| `INT2PTR` | dst | int | - | - | - | - | Integer to pointer |

### 5.5 Integer Arithmetic

All operate on the type encoded in `type_raw`. For vector types (`lanes > 0`), the operation is lane-wise.

| Op | r | a | b | c | imm | flags | Description |
|----|---|---|---|---|-----|-------|-------------|
| `ADD` | dst | lhs | rhs | - | - | nsw,nuw | Integer add |
| `SUB` | dst | lhs | rhs | - | - | nsw,nuw | Integer subtract |
| `MUL` | dst | lhs | rhs | - | - | nsw,nuw | Integer multiply |
| `SDIV` | dst | lhs | rhs | - | - | - | Signed divide |
| `UDIV` | dst | lhs | rhs | - | - | - | Unsigned divide |
| `SMOD` | dst | lhs | rhs | - | - | - | Signed modulo |
| `UMOD` | dst | lhs | rhs | - | - | - | Unsigned modulo |
| `NEG` | dst | src | - | - | - | - | Integer negate |

### 5.6 Bitwise

| Op | r | a | b | c | imm | flags | Description |
|----|---|---|---|---|-----|-------|-------------|
| `AND` | dst | lhs | rhs | - | - | - | Bitwise AND |
| `OR` | dst | lhs | rhs | - | - | - | Bitwise OR |
| `XOR` | dst | lhs | rhs | - | - | - | Bitwise XOR |
| `NOT` | dst | src | - | - | - | - | Bitwise NOT |
| `SHL` | dst | val | amt | - | - | nsw,nuw | Shift left |
| `LSHR` | dst | val | amt | - | - | - | Logical shift right |
| `ASHR` | dst | val | amt | - | - | - | Arithmetic shift right |
| `ROL` | dst | val | amt | - | - | - | Rotate left |
| `ROR` | dst | val | amt | - | - | - | Rotate right |

### 5.7 Float Arithmetic

| Op | r | a | b | c | imm | flags | Description |
|----|---|---|---|---|-----|-------|-------------|
| `FADD` | dst | lhs | rhs | - | - | - | Float add |
| `FSUB` | dst | lhs | rhs | - | - | - | Float subtract |
| `FMUL` | dst | lhs | rhs | - | - | - | Float multiply |
| `FDIV` | dst | lhs | rhs | - | - | - | Float divide |
| `FNEG` | dst | src | - | - | - | - | Float negate |
| `FABS` | dst | src | - | - | - | - | Float absolute value |
| `SQRT` | dst | src | - | - | - | - | Square root |
| `FMIN` | dst | lhs | rhs | - | - | - | Float minimum |
| `FMAX` | dst | lhs | rhs | - | - | - | Float maximum |

### 5.8 Comparisons

All produce an `FBT_I1` result (or vector of i1 for SIMD).

| Op | r | a | b | c | imm | flags | Description |
|----|---|---|---|---|-----|-------|-------------|
| `CMP_EQ` | dst | lhs | rhs | - | - | - | Equal |
| `CMP_NE` | dst | lhs | rhs | - | - | - | Not equal |
| `CMP_SLT` | dst | lhs | rhs | - | - | - | Signed less than |
| `CMP_SLE` | dst | lhs | rhs | - | - | - | Signed less or equal |
| `CMP_SGT` | dst | lhs | rhs | - | - | - | Signed greater than |
| `CMP_SGE` | dst | lhs | rhs | - | - | - | Signed greater or equal |
| `CMP_ULT` | dst | lhs | rhs | - | - | - | Unsigned less than |
| `CMP_ULE` | dst | lhs | rhs | - | - | - | Unsigned less or equal |
| `CMP_UGT` | dst | lhs | rhs | - | - | - | Unsigned greater than |
| `CMP_UGE` | dst | lhs | rhs | - | - | - | Unsigned greater or equal |
| `CMP_FEQ` | dst | lhs | rhs | - | - | - | Float ordered equal |
| `CMP_FNE` | dst | lhs | rhs | - | - | - | Float ordered not equal |
| `CMP_FLT` | dst | lhs | rhs | - | - | - | Float ordered less than |
| `CMP_FLE` | dst | lhs | rhs | - | - | - | Float ordered less or equal |
| `CMP_FGT` | dst | lhs | rhs | - | - | - | Float ordered greater than |
| `CMP_FGE` | dst | lhs | rhs | - | - | - | Float ordered greater or equal |

### 5.9 Conversions

| Op | r | a | b | c | imm | flags | Description |
|----|---|---|---|---|-----|-------|-------------|
| `SEXT` | dst | src | - | - | - | - | Sign extend (result type in `type_raw`) |
| `ZEXT` | dst | src | - | - | - | - | Zero extend |
| `TRUNC` | dst | src | - | - | - | - | Truncate |
| `FPEXT` | dst | src | - | - | - | - | Float widen (f16→f32, f32→f64) |
| `FPTRUNC` | dst | src | - | - | - | - | Float narrow (f64→f32, f32→f16) |
| `SI2FP` | dst | src | - | - | - | - | Signed integer → float |
| `UI2FP` | dst | src | - | - | - | - | Unsigned integer → float |
| `FP2SI` | dst | src | - | - | - | - | Float → signed integer |
| `FP2UI` | dst | src | - | - | - | - | Float → unsigned integer |
| `BITCAST` | dst | src | - | - | - | - | Reinterpret bits |

The source type is known from the source value. The destination type is in `type_raw`.

### 5.10 Select

| Op | r | a | b | c | imm | flags | Description |
|----|---|---|---|---|-----|-------|-------------|
| `SELECT` | dst | cond (i1) | true_val | false_val | - | - | `cond ? a : b` |

### 5.11 Control Flow

| Op | r | a | b | c | imm | flags | Description |
|----|---|---|---|---|-----|-------|-------------|
| `JUMP` | - | target block | - | - | - | - | Unconditional branch |
| `BRANCH` | - | cond (i1) | true_blk | false_blk | - | - | Conditional branch |
| `SWITCH` | - | key | default_blk | - | aux_idx\|count<<32 | - | Multi-way branch (cases in aux) |
| `RET` | - | val | - | - | - | - | Return (single value in `a`, FB_NOREG for void) |
| `UNREACHABLE` | - | - | - | - | - | - | Unreachable (no-return) |
| `TRAP` | - | - | - | - | - | - | Hardware trap |
| `DEBUGBREAK` | - | - | - | - | - | - | Debugger break |

For `BRANCH`, `a` is the condition value ID, `b` and `c` are block indices (not value IDs).

For `SWITCH`, cases are stored in the auxiliary operand pool:
```
aux[aux_idx + 0] = case_value_0 (i64, low 32)
aux[aux_idx + 1] = case_value_0 (i64, high 32)
aux[aux_idx + 2] = target_block_0
aux[aux_idx + 3] = case_value_1 (low 32)
...
```

For `RET`, the single return value ID is in `a` (or `FB_NOREG` for void return). Multi-return procedures use sret (hidden pointer argument) at the ABI level.

### 5.12 Function Calls

| Op | r | a | b | c | imm | flags | Description |
|----|---|---|---|---|-----|-------|-------------|
| `CALL` | dst | target | aux_start | arg_count | - | cc | Function call |
| `TAILCALL` | - | target | aux_start | arg_count | - | cc | Tail call |

`target` is a value ID (pointer to function). Arguments are in `aux[aux_start..aux_start+arg_count]`.

`flags` encodes calling convention:
```cpp
enum : u8 {
    FBCC_ODIN     = 0, // Odin calling convention (C + implicit context)
    FBCC_C        = 1, // C calling convention
    FBCC_STDCALL  = 2,
    FBCC_FASTCALL = 3,
};
```

The `r` field receives the return value. For void calls, `r = FB_NOREG`. For multi-return, `r` receives a pseudo-value that `PROJ` extracts from.

### 5.13 Multi-Value Projection

| Op | r | a | b | c | imm | flags | Description |
|----|---|---|---|---|-----|-------|-------------|
| `PROJ` | dst | multi | - | - | index | - | Extract element from multi-value |

Used after `CALL` with multiple return values, and after `ATOMIC_CAS` (value + success bool).

### 5.14 Atomics

| Op | r | a | b | c | imm | flags | Description |
|----|---|---|---|---|-----|-------|-------------|
| `ATOMIC_LOAD` | dst | ptr | - | - | align | order | Atomic load |
| `ATOMIC_STORE` | - | ptr | val | - | align | order | Atomic store |
| `ATOMIC_XCHG` | dst | ptr | val | - | align | order | Atomic exchange |
| `ATOMIC_ADD` | dst | ptr | val | - | align | order | Atomic fetch-add |
| `ATOMIC_SUB` | dst | ptr | val | - | align | order | Atomic fetch-sub |
| `ATOMIC_AND` | dst | ptr | val | - | align | order | Atomic fetch-and |
| `ATOMIC_OR` | dst | ptr | val | - | align | order | Atomic fetch-or |
| `ATOMIC_XOR` | dst | ptr | val | - | align | order | Atomic fetch-xor |
| `ATOMIC_CAS` | dst(multi) | ptr | expected | desired | align | order+fail | Atomic compare-exchange; PROJ 0=old val, PROJ 1=success (i1) |
| `FENCE` | - | - | - | - | - | order | Memory fence |

All atomic read-modify-write ops return the **old** value.

### 5.15 Bit Manipulation

| Op | r | a | b | c | imm | flags | Description |
|----|---|---|---|---|-----|-------|-------------|
| `BSWAP` | dst | src | - | - | - | - | Byte swap |
| `CLZ` | dst | src | - | - | - | - | Count leading zeros |
| `CTZ` | dst | src | - | - | - | - | Count trailing zeros |
| `POPCNT` | dst | src | - | - | - | - | Population count |

### 5.16 Wide Arithmetic

| Op | r(multi) | a | b | c | imm | flags | Description |
|----|----------|---|---|---|-----|-------|-------------|
| `ADDPAIR` | lo,hi | a_lo | a_hi | b_lo | *(b_hi in aux)* | - | Wide add |
| `MULPAIR` | lo,hi | lhs | rhs | - | - | - | Full-width multiply |

`ADDPAIR` needs 4 source operands. The fourth (`b_hi`) is stored at `aux[imm]`. Both return multi-values accessible via `PROJ 0` (lo) and `PROJ 1` (hi).

### 5.17 Vector (SIMD)

Arithmetic on vector types uses the standard opcodes (`ADD`, `FADD`, etc.) — the `lanes` field in `type_raw` signals SIMD lowering.

These opcodes are vector-specific:

| Op | r | a | b | c | imm | flags | Description |
|----|---|---|---|---|-----|-------|-------------|
| `VSHUFFLE` | dst | vec_a | vec_b | - | mask aux_idx | - | Shuffle lanes (mask in aux) |
| `VEXTRACT` | dst (scalar) | vec | - | - | lane index | - | Extract single lane |
| `VINSERT` | dst (vec) | vec | scalar | - | lane index | - | Insert into lane |
| `VSPLAT` | dst (vec) | scalar | - | - | - | - | Broadcast scalar to all lanes |

Shuffle mask: `aux[mask_idx + i]` = source lane index for result lane `i`. Lanes from `vec_a` are `0..N-1`, from `vec_b` are `N..2N-1`.

### 5.18 Miscellaneous

| Op | r | a | b | c | imm | flags | Description |
|----|---|---|---|---|-----|-------|-------------|
| `VA_START` | dst | alloca_ptr | - | - | - | - | C variadic: initialize va_list |
| `PREFETCH` | - | ptr | - | - | level (0-3) | - | Memory prefetch hint |
| `CYCLE` | dst (i64) | - | - | - | - | - | Read cycle counter |
| `ASM` | - | - | - | - | asm_data_idx | - | Inline assembly (data in aux) |

### 5.19 SSA (for future -O1)

| Op | r | a | b | c | imm | flags | Description |
|----|---|---|---|---|-----|-------|-------------|
| `PHI` | dst | region_blk | - | - | aux_idx\|count<<32 | - | SSA phi node |

Phi operands in aux: `aux[idx + 2*i] = predecessor_block, aux[idx + 2*i + 1] = value_id`.

**The -O0 builder never emits PHI.** All cross-block values go through alloca+load/store. PHI exists so that a future mem2reg pass can promote stack slots to SSA values in-place, without changing the IR format.

## 6. Blocks & Control Flow

```cpp
struct fbBlock {
    u32 first_inst;    // index into fbProc::insts[]
    u32 inst_count;    // number of instructions in this block
};
```

A block is a half-open range `[first_inst, first_inst + inst_count)` into the procedure's instruction array. The last instruction of every block must be a **terminator**: `JUMP`, `BRANCH`, `SWITCH`, `RET`, `UNREACHABLE`, or `TRAP`.

**No predecessor/successor lists.** Successors are encoded in the terminator's operands. Predecessors are not tracked — they're unnecessary at -O0 (no dataflow analysis). A future -O1 pass can compute them in O(N) if needed.

Blocks are numbered `0..block_count-1`. Block 0 is always the entry block. Block ordering is the builder's emission order (typically source order), which is also the lowering order. No block reordering.

## 7. Procedures

```cpp
struct fbStackSlot {
    u32     size;         // byte size
    u32     align;        // byte alignment
    i32     frame_offset; // assigned during lowering (negative from frame pointer)
    Entity *entity;       // Odin variable entity (NULL for temporaries)
    Type   *odin_type;    // for DWARF type info
    u32     scope_start;  // first instruction index where this slot is live
};

struct fbLoc {
    u32 file_id;  // index into fbModule::source_files[]
    u32 line;
    u16 column;
    u16 flags;    // FBL_IS_STMT, etc.
};

struct fbProc {
    // Identity
    Entity *entity;
    Type   *odin_type;      // procedure type
    String  name;            // mangled symbol name

    // IR storage (contiguous arrays)
    fbInst *insts;
    u32     inst_count;
    u32     inst_cap;

    fbBlock *blocks;
    u32      block_count;
    u32      block_cap;

    fbStackSlot *slots;
    u32          slot_count;
    u32          slot_cap;

    // Auxiliary operand pool (for CALL args, SWITCH cases, RET values, PHI operands)
    u32 *aux;
    u32  aux_count;
    u32  aux_cap;

    // Source location table (deduplicated)
    fbLoc *locs;
    u32    loc_count;
    u32    loc_cap;

    // SSA value counter (monotonically increasing, never recycled)
    u32 next_value;

    // Current block during IR construction
    u32 current_block;

    // Relocations (populated by lowering, consumed by object file emission)
    fbReloc *relocs;
    u32      reloc_count;
    u32      reloc_cap;

    // Parameter ABI: param_locs[i] maps the i-th GP register argument to a stack
    // slot and sub-offset within it. Two-eightbyte params (string, slice) share
    // a single 16-byte slot across two consecutive entries (sub_offset 0 and 8).
    struct fbParamLoc {
        u32 slot_idx;
        i32 sub_offset;  // 0 for first/only eightbyte, 8 for second
    };
    fbParamLoc *param_locs;
    u32         param_count;

    // Split return convention: split_returns_index is the first param_locs entry
    // for hidden output pointer parameters. split_returns_count is how many.
    i32 split_returns_index;
    i32 split_returns_count;

    // XMM parameter ABI (non-Odin CC only): maps SSE-classified float params
    // to XMM0-XMM7. The prologue spills these to stack slots.
    struct fbXmmParamLoc {
        u32 slot_idx;     // stack slot for spill
        u8  xmm_idx;     // XMM register number (0-7)
        u8  float_kind;   // FBT_F32 or FBT_F64
    };
    fbXmmParamLoc *xmm_param_locs;
    u32            xmm_param_count;

    // Machine code output (populated by lowering)
    u8    *machine_code;
    u32    machine_code_size;
    bool   is_foreign;
    bool   is_export;
};
```

**Value numbering:** `fbProc::next_value` starts at 0 and increments for every instruction that produces a value. Value IDs are globally unique within a procedure. `FB_NOREG` (0xFFFFFFFF) marks void-producing instructions.

**Stack slot assignment** during lowering:
1. Sort slots by alignment (largest first) for minimal padding. The sort uses an **index array** so that the `slots[]` array is never reordered — ALLOCA instructions reference slots by index, so in-place sorting would invalidate those references.
2. Assign negative offsets from the frame pointer (in sorted order): `slot[0]` at `-align(slot[0].size, slot[0].align)`, etc.
3. Total frame size = sum of aligned slot sizes + space for callee-saved registers + call argument area.

## 8. Module

```cpp
enum fbArch : u8 { FB_ARCH_X64, FB_ARCH_ARM64, FB_ARCH_UNKNOWN };
enum fbOS   : u8 { FB_OS_LINUX, FB_OS_WINDOWS, FB_OS_MACOS, FB_OS_FREEBSD, FB_OS_UNKNOWN };

struct fbTarget {
    fbArch arch;
    fbOS   os;
    u8     ptr_size;    // 8 for 64-bit
    u8     int_size;    // 8 for 64-bit
    // Feature flags (SSE4.2, AVX2, NEON, etc.) — from build_context
    u64    features;
};

struct fbSourceFile {
    String path;
    u32    id;         // matches AstFile::id for lookup
};

struct fbRodataEntry {
    u8    *data;
    u32    size;
    String name;   // symbol name (e.g. ".L.str.0")
};

// Abstract symbol index = FB_GLOBAL_SYM_BASE + global_entries index.
enum : u32 { FB_GLOBAL_SYM_BASE = 0x40000000 };

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

    // All procedures (built in parallel, lowered in parallel)
    // Abstract symbol index for proc i = i.
    Array<fbProc *>   procs;
    BlockingMutex     procs_mutex;

    // Legacy symbol table (being phased out)
    Array<fbSymbol>   symbols;
    StringMap<u32>    symbol_map;
    BlockingMutex     symbols_mutex;

    // Read-only data (string literals, etc.)
    // Abstract symbol index for rodata entry i = procs.count + i.
    Array<fbRodataEntry>  rodata_entries;
    StringMap<u32>        string_intern_map;  // string content → rodata entry index

    // Global variables (package-level).
    // Abstract symbol index for global entry i = FB_GLOBAL_SYM_BASE + i.
    Array<fbGlobalEntry>      global_entries;
    PtrMap<Entity *, u32>     global_entity_map;  // Entity* → global_entries index

    // Source file registry
    Array<fbSourceFile>        source_files;
    PtrMap<uintptr, u32>       file_id_to_idx;  // AstFile::id → source_files index
    fbSymbol *type_info_names;
    fbSymbol *type_info_offsets;
    fbSymbol *type_info_usings;
    fbSymbol *type_info_tags;
};
```

**Thread safety:** Procedure IR construction and lowering can be parallelized. `procs_mutex` and `symbols_mutex` protect shared state. Per-procedure data (instructions, blocks, slots) is thread-local to the building thread — no synchronization needed within a procedure.

**Module-level arena** is not yet implemented. The module currently uses `heap_allocator()` for all allocations. A future phase will add arena allocation (see §13).

## 9. Values & Addresses (Builder Types)

These types exist in the **builder layer only** — they are not part of the IR. They carry Odin type information needed for semantic lowering (ABI decisions, field offsets, debug info).

```cpp
// An SSA value reference. 8 bytes. Passed by value.
struct fbValue {
    u32    id;       // virtual register number (FB_NOREG for void)
    Type  *type;     // Odin type (for builder's type-directed lowering)
};

// An addressable location in the builder's model.
// Resolved to IR primitives (LOAD, STORE, MEMBER, CALL, etc.) on use.
enum fbAddrKind : u8 {
    fbAddr_Default,          // simple pointer
    fbAddr_Map,              // runtime map access (key → call map_get_ptr → pointer)
    fbAddr_Context,          // implicit context field (ctx_ptr + field offset chain)
    fbAddr_SOA,              // struct-of-arrays (parallel arrays, indexed)
    fbAddr_RelativePtr,      // relative pointer (base + *offset)
    fbAddr_RelativeSlice,    // relative slice (relative ptr + length)
    fbAddr_Swizzle,          // vector component reorder (up to 4)
    fbAddr_SwizzleLarge,     // vector component reorder (arbitrary count)
    fbAddr_BitField,         // sub-byte field (shift + mask)
};

struct fbAddr {
    fbAddrKind kind;
    fbValue    base;       // for Default: the pointer itself
    Type      *type;       // the Odin type of the addressed value

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
```

**Address resolution** happens in the builder. When `fb_addr_load()` is called on an `fbAddr`, the builder emits the appropriate IR instruction sequence:

| Kind | Load sequence |
|------|---------------|
| Default | `LOAD base` |
| Map | `CALL __dynamic_map_get_ptr(map, &key)` → `LOAD result` |
| Context | `MEMBER ctx_ptr, field_offset` → `LOAD` (chained for nested selection) |
| SOA | For each field: `LOAD base_ptr[field]` → `ARRAY ptr, index, stride` → `LOAD` |
| RelativePtr | `LOAD base` (gets relative offset) → `ADD base, offset` → `LOAD` |
| Swizzle | Multiple `VEXTRACT` + `VINSERT` |
| BitField | `LOAD` → `LSHR, bit_offset` → `AND, mask` → `TRUNC` if needed |

## 10. Builder API

The builder walks the Odin AST (post-checking) and emits IR instructions. It mirrors the structure of the existing `cg_build_*` functions from the Tilde backend.

### 10.1 Procedure Construction

```cpp
// Lifecycle
fb_proc_create(fbModule *m, Entity *entity) → fbProc*
fb_proc_begin(fbBuilder *b, fbProc *p)
fb_proc_end(fbBuilder *b)

// Block management
fb_block_create(fbBuilder *b) → u32           // returns block index
fb_block_set(fbBuilder *b, u32 block_id)      // set current insertion block
fb_block_current(fbBuilder *b) → u32          // get current block index
fb_block_is_terminated(fbBuilder *b) → bool   // does current block end with a terminator?
```

### 10.2 Constants

```cpp
fb_const_int(fbBuilder *b, Type *t, i64 value) → fbValue
fb_const_uint(fbBuilder *b, Type *t, u64 value) → fbValue
fb_const_float(fbBuilder *b, Type *t, f64 value) → fbValue
fb_const_bool(fbBuilder *b, bool value) → fbValue
fb_const_nil(fbBuilder *b, Type *t) → fbValue
fb_const_undef(fbBuilder *b, Type *t) → fbValue
fb_sym_addr(fbBuilder *b, u32 sym_idx, Type *t) → fbValue
```

**Constant folding** is performed during construction:
```cpp
fbValue fb_add(fbBuilder *b, fbValue lhs, fbValue rhs) {
    // If both operands are ICONST, fold at build time:
    if (b->insts[lhs.id].op == FB_ICONST && b->insts[rhs.id].op == FB_ICONST) {
        return fb_const_int(b, lhs.type, b->insts[lhs.id].imm + b->insts[rhs.id].imm);
    }
    // Identity: x + 0 → x
    if (is_zero_const(b, rhs)) return lhs;
    if (is_zero_const(b, lhs)) return rhs;
    // Otherwise emit ADD instruction
    return fb_emit(b, FB_ADD, fb_type_of(lhs), lhs.id, rhs.id, 0, 0);
}
```

This is **builder-side peephole optimization**, not an IR pass. It happens during construction with zero additional cost (just a few `if` checks per instruction). It eliminates trivially dead code and reduces instruction count without any post-construction analysis.

### 10.3 Memory

```cpp
fb_alloca(fbBuilder *b, Type *t, Entity *e) → fbValue  // allocate stack slot for variable
fb_load(fbBuilder *b, fbValue ptr, Type *t) → fbValue
fb_store(fbBuilder *b, fbValue ptr, fbValue val)
fb_memcpy(fbBuilder *b, fbValue dst, fbValue src, fbValue size, u32 align)
fb_memset(fbBuilder *b, fbValue dst, fbValue val, fbValue size, u32 align)
fb_memzero(fbBuilder *b, fbValue dst, fbValue size, u32 align)
```

### 10.4 Pointer Arithmetic

```cpp
fb_member(fbBuilder *b, fbValue base, i64 offset, Type *result_type) → fbValue
fb_array_access(fbBuilder *b, fbValue base, fbValue index, i64 stride) → fbValue
fb_ptr2int(fbBuilder *b, fbValue ptr) → fbValue
fb_int2ptr(fbBuilder *b, fbValue int_val, Type *ptr_type) → fbValue
```

### 10.5 Arithmetic, Bitwise, Float, Compare, Convert

```cpp
// Arithmetic (integer or vector, based on operand type)
fb_add(fbBuilder *b, fbValue lhs, fbValue rhs) → fbValue
fb_sub, fb_mul, fb_sdiv, fb_udiv, fb_smod, fb_umod, fb_neg → fbValue

// Bitwise
fb_and, fb_or, fb_xor, fb_not → fbValue
fb_shl, fb_lshr, fb_ashr, fb_rol, fb_ror → fbValue

// Float
fb_fadd, fb_fsub, fb_fmul, fb_fdiv, fb_fneg, fb_fabs, fb_sqrt, fb_fmin, fb_fmax → fbValue

// Compare
fb_cmp(fbBuilder *b, fbCmpKind kind, fbValue lhs, fbValue rhs) → fbValue  // returns i1

// Convert
fb_sext, fb_zext, fb_trunc → fbValue
fb_fpext, fb_fptrunc → fbValue
fb_si2fp, fb_ui2fp, fb_fp2si, fb_fp2ui → fbValue
fb_bitcast(fbBuilder *b, fbValue src, Type *dst_type) → fbValue

// Select
fb_select(fbBuilder *b, fbValue cond, fbValue t, fbValue f) → fbValue
```

### 10.6 Control Flow

```cpp
fb_jump(fbBuilder *b, u32 target_block)
fb_branch(fbBuilder *b, fbValue cond, u32 true_block, u32 false_block)
fb_switch(fbBuilder *b, fbValue key, u32 default_block, Slice<fbSwitchCase> cases)
fb_ret(fbBuilder *b, Slice<fbValue> values)
fb_ret_void(fbBuilder *b)
fb_unreachable(fbBuilder *b)
fb_trap(fbBuilder *b)
fb_debugbreak(fbBuilder *b)
```

### 10.7 Calls

```cpp
fb_call(fbBuilder *b, fbValue target, Slice<fbValue> args, Type *result_type) → fbValue
fb_tailcall(fbBuilder *b, fbValue target, Slice<fbValue> args)
fb_proj(fbBuilder *b, fbValue multi, u32 index, Type *elem_type) → fbValue
```

**ABI lowering** is handled in the builder, not the IR. Before emitting `CALL`, the builder:
1. Classifies each argument per the platform ABI (direct in register, indirect via pointer, split across registers).
2. For structs passed indirectly: `ALLOCA` a temp, `MEMCPY` the struct, pass the pointer.
3. For structs passed in registers: `LOAD` each register-sized chunk.
4. For struct returns: `ALLOCA` space, pass pointer as hidden first arg (sret).

The IR-level `CALL` instruction sees only scalar/pointer arguments — all ABI decomposition has already happened.

### 10.8 Address Operations (Odin Semantic Layer)

```cpp
fb_addr(fbValue ptr) → fbAddr                              // simple pointer address
fb_addr_map(fbValue base, fbValue key, Type *map_type, Type *result) → fbAddr
fb_addr_context(fbBuilder *b, Selection sel) → fbAddr
fb_addr_soa(fbValue base, fbValue index, Ast *expr) → fbAddr
fb_addr_relative(fbValue base, bool deref) → fbAddr
fb_addr_swizzle(fbValue base, Type *type, u8 count, u8 *indices) → fbAddr
fb_addr_bitfield(fbValue base, u32 bit_offset, u32 bit_count) → fbAddr

fb_addr_load(fbBuilder *b, fbAddr addr) → fbValue           // resolve addr → LOAD sequence
fb_addr_store(fbBuilder *b, fbAddr addr, fbValue val)        // resolve addr → STORE sequence
fb_addr_get_ptr(fbBuilder *b, fbAddr addr) → fbValue         // get raw pointer (if possible)
```

### 10.9 Source Location

```cpp
fb_set_loc(fbBuilder *b, TokenPos pos)  // all subsequent instructions get this location
```

The builder deduplicates locations: if the new pos matches the current one, no table entry is added. The location index is stamped into every emitted instruction's `loc` field.

### 10.10 Builder State

```cpp
struct fbBuilder {
    fbProc   *proc;
    fbModule *module;

    // Current insertion point
    u32 current_block;
    u32 current_loc;        // index into proc->locs

    // Odin entity
    Entity   *entity;
    Type     *type;
    Ast      *body;
    DeclInfo *decl;

    // Scoping & control flow (mirrors cgProcedure)
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
```

## 11. Machine Lowering

The lowering is a **single forward pass** over each procedure's blocks. No global analysis. Each block is lowered independently.

### 11.1 Register State (Block-Local)

```cpp
struct fbRegState {
    u32  vreg;        // which IR value is in this register (FB_NOREG if free)
    u32  last_use;    // instruction index of last use (for eviction policy)
    bool dirty;       // modified since last spill?
};

enum : i32 { FB_LOC_NONE = INT32_MIN };

struct fbStackLayout {
    u32 total_frame_size;  // total bytes subtracted from RSP (16-aligned)
    u32 slot_area_size;    // bytes used by stack slots
};

struct fbLowCtx {
    fbProc   *proc;
    fbModule *module;

    // Code emission buffer
    u8  *code;
    u32  code_count;
    u32  code_cap;

    // Block-start code offsets (for branch patching)
    u32 *block_offsets;

    // Machine register file (GP only — XMM scratch registers are not tracked)
    fbRegState gp[16];    // x64: RAX-R15

    // Where is each value? (vreg → location)
    // Indexed by value ID. Entries:
    //   >= 0: machine register index
    //   < 0:  stack frame offset (negative RBP displacement)
    //   FB_LOC_NONE: not yet materialized
    i32 *value_loc;
    u32  value_loc_count;

    // Current instruction index (for LRU last_use tracking)
    u32 current_inst_idx;

    // Forward branch fixups (all rel32)
    fbFixup *fixups;
    u32      fixup_count;
    u32      fixup_cap;

    // Call relocations (accumulated during lowering, copied to fbProc)
    fbReloc *relocs;
    u32      reloc_count;
    u32      reloc_cap;

    // Symbol references: value_sym[vreg] = proc index when vreg is a SYMADDR.
    // FB_NOREG means the vreg is not a symbol reference.
    u32     *value_sym;

    // Stack frame layout
    fbStackLayout frame;
};
```

### 11.2 Register Allocation Strategy

At -O0, the allocator is **block-local greedy with LRU eviction**:

```
for each block B in procedure:
    clear register state (all regs free)
    for each instruction I in B:
        1. RESOLVE SOURCES: for each source operand of I:
           - if value is in a register → use it, update last_use
           - if value is on the stack → pick a free register, emit LOAD from stack
           - if no free register → evict LRU register (emit STORE if dirty), then LOAD
        2. ALLOCATE DESTINATION: for I's result:
           - pick a free register (prefer caller-saved), excluding source registers
           - if none free → evict LRU (excluding source registers)
           - mark register as holding this value
        3. EMIT: encode the machine instruction using resolved machine registers
        4. SPILL BEFORE CALLS: before CALL instructions, spill all caller-saved
           registers that hold live values
    end block:
        spill all dirty registers to stack (value_loc consistency)
        clear register state (all regs free — block-local invariant)
```

**Block-boundary spills:** At block boundaries, `reset_regs` iterates the allocatable registers and spills any dirty values *before* clearing register state. This ensures `value_loc` accurately reflects that values are on the stack, not in registers that are about to be invalidated. Without this, cross-block control flow produces wrong code because `value_loc` claims a value is in a register that the next block will overwrite.

**Exclude mask:** `alloc_gp` and `resolve_gp` accept a `u16 exclude_mask` (one bit per hardware register) that prevents the allocator from choosing or evicting specific registers. This is critical for multi-operand instructions where allocating the destination must not evict a source. For example, `ADD %r, %a, %b` resolves `%a` and `%b` first, then allocates `%r` with `exclude_mask = (1 << ra) | (1 << rb)`. The same mechanism supports instructions that require specific physical registers (e.g., shifts need RCX for the count, division uses RAX:RDX). A dedicated `move_value_to_reg` helper handles the "place this value in this exact register" pattern for shifts and division.

**Ownership invariant:** `resolve_gp` asserts that when `value_loc[vreg]` says a value is in register R, then `gp[R].vreg == vreg`. It also asserts that a value has either a valid location (register or spill slot) or a symbol reference — values with `FB_LOC_NONE` and no symbol are programming errors caught at lowering time rather than producing silent wrong code.

**Dirty tracking:** A register is "dirty" when it holds a value that has not been written to its spill slot. `move_value_to_reg` marks values as dirty when moved from another register (`loc >= 0`) or freshly materialized (`loc == FB_LOC_NONE`, e.g. SYMADDR via RIP-relative LEA). Values reloaded from spill slots (`loc < 0 && loc != FB_LOC_NONE`) are clean since the spill slot already contains the correct value. Eviction only emits a store for dirty registers, so incorrect dirty tracking causes silent data loss.

**Division protocol:** Integer division (`SDIV`/`UDIV`/`SMOD`/`UMOD`) requires the dividend in RAX and clobbers both RAX and RDX. The lowering: (1) spills RAX and RDX, (2) moves the dividend to RAX via `move_value_to_reg`, (3) flushes RAX to the dividend's spill slot if dirty, (4) detaches the dividend from RAX (`value_loc[a] = spill_offset, gp[RAX].vreg = FB_NOREG`) *before* the DIV instruction executes. Without step (3-4), DIV overwrites RAX and `value_loc` is left pointing at a register whose contents have been destroyed.

**Scratch register reservation:** On x64, RSP and RBP are reserved (frame/stack). On arm64, SP and X29 (FP) are reserved. All other registers are available for allocation.

**Callee-saved registers:** At -O0, avoid callee-saved registers entirely (no save/restore overhead). Use only caller-saved registers: x64: RAX, RCX, RDX, RSI, RDI, R8-R11 (9 GP). arm64: X0-X17 (18 GP), V0-V7 (8 FP).

**XMM scratch registers:** Float values are stored in GP registers at -O0 (as bit-punned i32/i64). XMM0 and XMM1 are used as **fixed scratch registers** for float computation — operands are moved GP→XMM before SSE instructions, results are moved XMM→GP after. No XMM register allocator or tracking is needed. This simplifies the design significantly at the cost of extra MOVD/MOVQ transfers per float operation, which is acceptable for -O0.

### 11.3 Code Emission

The lowering for each instruction is a fixed template. Example (x64, `FB_ADD i64 %r, %a, %b`):

```cpp
case FB_ADD: {
    Reg ra = resolve_gp(ctx, inst.a);     // ensure %a is in a GP register
    Reg rb = resolve_gp(ctx, inst.b);     // ensure %b is in a GP register
    Reg rd = alloc_gp(ctx, inst.r);       // allocate register for result
    if (rd != ra) emit_mov(ctx, rd, ra);  // mov rd, ra  (if not same register)
    emit_add_rr(ctx, rd, rb);             // add rd, rb
    break;
}
```

ARM64 equivalent:
```cpp
case FB_ADD: {
    Reg ra = resolve_gp(ctx, inst.a);
    Reg rb = resolve_gp(ctx, inst.b);
    Reg rd = alloc_gp(ctx, inst.r);
    emit_add_rrr(ctx, rd, ra, rb);        // ADD Xd, Xa, Xb (three-address)
    break;
}
```

### 11.4 Relocations

Call and symbol reference instructions produce relocations that the object file emitter resolves:

```cpp
enum fbRelocType : u32 {
    FB_RELOC_PC32  = 2,   // R_X86_64_PC32
    FB_RELOC_PLT32 = 4,   // R_X86_64_PLT32
};

struct fbReloc {
    u32         code_offset;   // byte offset in this proc's machine code
    u32         target_sym;    // abstract symbol index (proc, rodata, or FB_GLOBAL_SYM_BASE + gidx)
    i64         addend;        // typically -4
    fbRelocType reloc_type;
};
```

`SYMADDR` instructions are tracked via `value_sym[vreg] = abstract_sym_index` in the lowering context. When `resolve_gp` encounters a value with no location but a valid `value_sym` entry, it materializes it as a RIP-relative LEA. Direct calls (`FB_CALL` where the target has a `value_sym` entry) emit `CALL rel32` with a `PLT32` relocation instead of an indirect `CALL r/m64`.

### 11.5 Branch Patching

Forward branches (to blocks not yet emitted) record a fixup:
```cpp
struct fbFixup {
    u32 code_offset;     // where the rel32 displacement is in the code buffer
    u32 target_block;    // which block it branches to
};
```

All fixups are rel32 format (x64). Backward branches (to already-emitted blocks) compute the displacement immediately. After all blocks are emitted, iterate fixups and patch forward references:
```cpp
for (u32 i = 0; i < ctx->fixup_count; i++) {
    fbFixup *f = &ctx->fixups[i];
    i32 disp = block_offsets[f->target_block] - (f->code_offset + 4);
    memcpy(code + f->code_offset, &disp, 4);
}
```

### 11.6 Prologue / Epilogue

Emitted after all blocks (frame size is known):

**x64 prologue:**
```asm
push rbp
mov rbp, rsp
sub rsp, frame_size      ; aligned to 16 (imm8 when ≤127)
; Parameter spills: store ABI arg registers into their param stack slots
mov [rbp+slot_offset+sub_offset_0], rdi   ; 1st GP arg
mov [rbp+slot_offset+sub_offset_1], rsi   ; 2nd GP arg
...                                        ; up to 6 GP args (SysV)
```

Single-eightbyte parameters get an 8-byte / 8-aligned slot (`sub_offset = 0`). Two-eightbyte parameters (string, slice — classified as 2×INTEGER by the SysV ABI) share a single 16-byte / 8-aligned slot across two consecutive `param_locs` entries (`sub_offset` 0 and 8), so the two registers are stored contiguously. If both eightbytes of a two-eightbyte param cannot fit in the remaining GP registers, the entire argument falls back to stack passing. The SysV ABI leaves upper bits of narrow parameters undefined, so the full register is stored and the IR type system governs load width during the procedure body.

**x64 epilogue** (before each RET):
```asm
mov rsp, rbp
pop rbp
ret
```

**arm64 prologue:**
```asm
stp x29, x30, [sp, #-frame_size]!
mov x29, sp
```

**arm64 epilogue:**
```asm
ldp x29, x30, [sp], #frame_size
ret
```

The prologue is prepended to the code buffer after block emission. All code offsets (block_offsets, fixups, line table) are adjusted by the prologue size.

### 11.7 Float Lowering (x64)

Float values live in GP registers as bit-punned integers. XMM0 and XMM1 are fixed scratch registers — no XMM allocation or tracking.

**Float binary arithmetic** (`FADD`, `FSUB`, `FMUL`, `FDIV`, `FMIN`, `FMAX`):
```
resolve %a → GP ra;  MOVD/MOVQ ra → XMM0
resolve %b → GP rb;  MOVD/MOVQ rb → XMM1
SSE_op XMM0, XMM1    (prefix F3 for f32, F2 for f64)
alloc  %r → GP rd;   MOVD/MOVQ XMM0 → rd
```

**Float unary** (`FNEG`, `FABS`, `SQRT`):
- `FNEG`: XOR sign bit via GP (xor with `0x80000000` / `0x8000000000000000`)
- `FABS`: AND away sign bit via GP (and with `0x7FFFFFFF` / `0x7FFFFFFFFFFFFFFF`)
- `SQRT`: GP→XMM0, `SQRTSS`/`SQRTSD`, XMM0→GP

**Float comparisons** (`CMP_FEQ..CMP_FGE`):
Uses `UCOMISS`/`UCOMISD` which sets ZF, CF, and PF. PF=1 when either operand is NaN.
- `FGT` (`seta`) and `FGE` (`setae`) are naturally NaN-safe (return false for NaN).
- `FEQ`: `sete` + `setnp` + `AND` (ordered and equal)
- `FNE`: `setne` + `setp` + `OR` (unordered or not-equal)
- `FLT`: `setb` + `setnp` + `AND` (ordered and below)
- `FLE`: `setbe` + `setnp` + `AND` (ordered and below-or-equal)

A `fb_x64_float_cmp_nan_safe` helper factors the four NaN-unsafe patterns.

**Float conversions:**
- `SI2FP`: `CVTSI2SS`/`CVTSI2SD`. Sub-i32 sources (i8, i16) require `MOVSX` sign-extension first — `LOAD` uses `MOVZX` (zero-extension), so without the sign-extend, `i8(-1)` = `0xFF` converts as 255.0 instead of -1.0.
- `UI2FP`: Full u64 range via halving trick. If the sign bit is set (value ≥ 2^63): halve with round-to-odd (`shr 1` + `or` low bit), convert signed, then `addss`/`addsd` to double the result. If positive: direct signed `CVTSI2SS`/`CVTSI2SD`. Uses `test reg,reg` + `jns` with in-place rel8 patching.
- `FP2UI`: Full u64 range via conditional subtraction. Load 2^63 as float into XMM1, `comiss`/`comisd`. If below: direct signed `CVTTSS2SI`/`CVTTSD2SI`. If above: subtract 2^63 float, convert signed, `btc rd,63` to toggle bit 63 back. Uses `jb` + `jmp` with in-place rel8 patching.
- `FP2SI`: `CVTTSS2SI`/`CVTTSD2SI` with truncation toward zero.
- `FPEXT` (f32→f64): `CVTSS2SD`
- `FPTRUNC` (f64→f32): `CVTSD2SS`

**Float parameters:** Float parameters classified as `FB_ABI_SSE` are routed through GP registers for intra-backend Odin-to-Odin calls (Odin CC convention). For external C calls (non-Odin CC), SSE-classified float params are received in XMM0-XMM7 and spilled to stack slots in the prologue. At call sites, SSE arguments are tracked with an `sse_mask`/`f64_mask` bitmask pair encoded in the CALL instruction's `imm` field; the lowering loads them from GP spill slots into XMM registers via `movd`/`movq` before the call. Non-Odin CC calls with SSE return types capture from XMM0 and transfer to a GP register.

### 11.8 Bit Manipulation Lowering (x64)

- `BSWAP`: `BSWAP r64` (0F C8+rd) — single instruction, result in-place
- `POPCNT`: `POPCNT r64, r64` (F3 0F B8 /r) — requires POPCNT feature flag
- `CLZ`: `BSR r64, r64` then `XOR result, 63` — BSR finds highest set bit, XOR inverts to count from MSB
- `CTZ`: `BSF r64, r64` (0F BC /r) — scans from LSB

## 12. Debug Info

### 12.1 DWARF (Linux, macOS)

At -O0, DWARF generation is straightforward because every variable has a **single, stable stack location** for its entire lifetime.

**Per variable:**
```
DW_TAG_variable
  DW_AT_name: "x"
  DW_AT_type: <type DIE ref>
  DW_AT_location: DW_OP_fbreg(-24)   // constant offset from frame pointer
```

No location lists. No register tracking. No range splits. This is the major simplification -O0 gives us.

**Per function:**
```
DW_TAG_subprogram
  DW_AT_name: "main"
  DW_AT_low_pc: <function start>
  DW_AT_high_pc: <function end>
  DW_AT_frame_base: DW_OP_reg6 (RBP on x64) / DW_OP_reg29 (X29 on arm64)
```

**Line number program:** Generated from `fbProc::locs[]` combined with code offsets from lowering. Maps code offsets to source lines. The line table is naturally ordered (we emit code in source order at -O0).

**Type DIEs:** Derived from Odin `Type*` pointers. The mapping from Odin types to DWARF type DIEs mirrors the existing `cg_debug_type()` and `lb_debug_type()` implementations. Cached per-module to avoid duplication.

**Scopes:** Odin's `Scope` tree maps directly to `DW_TAG_lexical_block` entries. Each scope's range is determined by the first and last instruction indices within that scope, mapped to code offsets via the line table.

### 12.2 CodeView (Windows)

Similar strategy. S_LOCAL records with `DefRangeFramePointerRelFullScope` (simple frame-pointer-relative, entire function scope). The simplicity of -O0 means we avoid the complex S_DEFRANGE variants.

## 13. Memory Management

**Current: heap allocation.** All IR data for a procedure (instructions, blocks, stack slots, aux operands, locations) is allocated via `heap_allocator()` with growable arrays (default capacities: 64 insts, 8 blocks, 16 slots, 32 aux, 16 locs). Foreign procedure declarations skip all array allocations since they have no IR bodies.

**Foreign proc optimization.** `fb_proc_create` detects `is_foreign` and skips the 5 heap allocations for instruction/block/slot/aux/loc arrays. All pointers remain NULL, capacities stay 0. `fb_proc_destroy`'s null checks handle cleanup. This is significant because foreign procs can vastly outnumber defined procs.

**Lowering temporaries.** The `fbLowCtx` struct allocates its own code buffer, block offsets, value location tracking, fixups, relocations, and symbol reference arrays per-procedure. These are freed after machine code is copied to the proc.

**Future: arena-per-procedure.** The design target is arena allocation where all procedure data is allocated from a per-procedure arena and freed at once after machine code emission. This eliminates individual `free()` calls, prevents fragmentation, and enables natural parallelism (each thread has its own arena).

## 14. Source File Organization

```
src/
├── fb_ir.h                 // IR types, opcode enum, instruction format, builder/lowering structs (~820 lines)
├── fb_ir.cpp               // Module lifecycle, type helpers, symbol management (~596 lines)
├── fb_build.cpp            // AST → IR builder (~3720 lines, growing)
│                           //   fb_build_expr(), fb_build_stmt(), fb_build_addr(),
│                           //   fb_build_call(), fb_build_return(), fb_emit_conv(), etc.
│                           //   Mirrors tilde_expr.cpp + tilde_stmt.cpp + tilde_proc.cpp
├── fb_abi.cpp              // ABI classification for SysV AMD64 (~172 lines, struct/array decomposition)
├── fb_lower_x64.cpp        // x86-64 machine code lowering (~2226 lines)
│                           //   GP register allocator, XMM scratch/ABI encoding helpers,
│                           //   float/int/bitmanip lowering, NaN-safe float comparisons,
│                           //   UI2FP halving trick, FP2UI conditional subtraction
├── fb_emit_elf.cpp         // ELF object file emission (~700 lines)
│                           //   Self-contained ELF64 types (no system elf.h dependency)
│                           //   fbBuf growable byte buffer for section construction
│                           //   .text, .rodata, .data, .bss, .rela.text sections
│                           //   Single-pass symbol table with proper LOCAL/GLOBAL ordering
├── fb_build_builtin.cpp    // Built-in procedure handling (~473 lines)
│                           //   len/cap/raw_data for slices, strings, dynamic arrays
│                           //   min/max (variadic), abs, clamp
│                           //   ptr_offset, ptr_sub, mem_copy, mem_zero
│                           //   trap/debug_trap/unreachable, expect, bswap
│                           //   count_ones/zeros, count_leading/trailing_zeros
│                           //   read_cycle_counter, cpu_relax
├── fb_build_const.cpp      // (planned) Constant value IR generation
├── fb_build_type_info.cpp  // (planned) Runtime type info global generation
├── fb_lower_arm64.cpp      // (planned) ARM64 machine code lowering
├── fb_emit_pe.cpp          // (planned) PE/COFF object file + CodeView emission
└── fb_emit_macho.cpp       // (planned) Mach-O object file + DWARF emission
```

**Platform gating:** `ALLOW_FAST_BACKEND` is defined only on Linux and FreeBSD (platforms with ELF emission support). The arch is checked at runtime — only x86-64 is currently supported; other architectures produce a clear error.

**Inclusion order** in `src/main.cpp`:
```cpp
#if ALLOW_FAST_BACKEND
#include "fb_ir.cpp"
#include "fb_abi.cpp"
#include "fb_build.cpp"
#include "fb_build_builtin.cpp"
#include "fb_lower_x64.cpp"
#include "fb_emit_elf.cpp"
#endif
```

**Main dispatch** in `src/main.cpp`:
```cpp
#if ALLOW_FAST_BACKEND
    if (build_context.fast_backend) {
        if (!fb_generate_code(checker, linker_data)) return 1;
        linker_stage(linker_data);
        export_linked_libraries(linker_data);
    } else
#endif
#if ALLOW_TILDE
    if (build_context.tilde_backend) { ... } else
#endif
    { /* LLVM backend */ }
```

## 15. Example: Odin to IR Translation

### Input
```odin
add_one :: proc(x: int) -> int {
    result := x + 1
    return result
}
```

### IR Output
```
proc @example.add_one(i64) -> i64 {
bb0:                                          ; entry
    %0 = ALLOCA   ptr    size=8 align=8       ; stack slot for 'x' parameter
    %1 = ALLOCA   ptr    size=8 align=8       ; stack slot for 'result'
    STORE          ptr %0, i64 %arg0, align=8 ; spill parameter to stack
    %2 = LOAD     i64    ptr %0, align=8      ; load x
    %3 = ICONST   i64    1                    ; constant 1
    %4 = ADD      i64    %2, %3              ; x + 1
    STORE          ptr %1, i64 %4, align=8    ; result := x + 1
    %5 = LOAD     i64    ptr %1, align=8      ; load result for return
    RET            i64 %5                      ; return result
}
```

At -O0, this is the complete IR. Every variable (`x`, `result`) has a stack slot. The debugger can inspect both at any point.

With a future mem2reg pass (-O1), this would become:
```
proc @example.add_one(i64) -> i64 {
bb0:
    %0 = ICONST   i64    1
    %1 = ADD      i64    %arg0, %0
    RET            i64 %1
}
```

Same IR format, no structural changes — just fewer instructions.

## 16. Opcode Summary Table

```
Opcode          Category         Count
─────────────────────────────────────
ICONST..UNDEF   Constants          4
ALLOCA          Stack              1
LOAD..MEMZERO   Memory             5
MEMBER..INT2PTR Pointer arith      4
ADD..NEG        Int arithmetic     8
AND..ROR        Bitwise            9
FADD..FMAX      Float arith        9
CMP_*           Comparisons       16
SEXT..BITCAST   Conversions       10
SELECT          Select             1
JUMP..DEBUGBR   Control flow       7
CALL, TAILCALL  Calls              2
PROJ            Multi-value        1
ATOMIC_*,FENCE  Atomics           10
BSWAP..POPCNT   Bit manip          4
ADDPAIR,MULPAIR Wide arith         2
VSHUFFLE..VSPL  Vector             4
VA_START..ASM   Misc               4
PHI             SSA (future)       1
─────────────────────────────────────
TOTAL                            ~102
```

~100 opcodes. Each maps 1:1 to a fixed machine instruction template.
The switch dispatch in the lowering loop handles all of them in ~2200 lines
per target (x64 currently at ~2226 lines; arm64 not yet implemented).

## 17. Design Invariants

1. **SSA property:** Every value ID is defined by exactly one instruction. The builder enforces this via a monotonic counter.

2. **Block termination:** Every block's last instruction is a terminator. The builder asserts this at `fb_proc_end()`.

3. **No cross-block register values (at -O0):** At the IR level, cross-block communication goes through alloca+load/store. At the machine level, the lowerer's `reset_regs` spills all dirty registers to stack at block boundaries, ensuring `value_loc` consistency before clearing register state. This is a -O0 convention — a future -O1 path may relax it via phi nodes.

4. **Dominance (weak):** Every use of a value is in the same block as its definition, or in a block reachable (transitively via block ordering) from the defining block. At -O0 with alloca+load/store, this is trivially satisfied since cross-block communication goes through memory.

5. **Type consistency:** Operands to binary operations have matching types. The builder asserts this. Conversions (SEXT, ZEXT, etc.) are explicit.

6. **Memory alignment:** Every LOAD, STORE, and ALLOCA specifies an alignment. The lowering trusts these values for instruction selection (aligned vs unaligned moves, vector alignment).

## 18. Implementation Status

### Phase 1: IR Infrastructure (DONE)

Implemented the complete IR type system, opcode enum (102 opcodes), instruction format (32-byte fixed), and all supporting data structures.

**Files created:**
- `src/fb_ir.h` — All IR types, opcode enum, instruction format, module/proc/builder structs, forward declarations
- `src/fb_ir.cpp` — Type helpers (`fb_data_type`, `fb_type_size`, etc.), target detection, module lifecycle
- `src/main.cpp` — `ALLOW_FAST_BACKEND` flag, `-fast` CLI flag, `#include` wiring

**What works:** Compiler builds with the fast backend infrastructure. `-fast` flag is accepted. Module creation and destruction work.

### Phase 2: Empty Proc End-to-End (DONE)

Complete pipeline: iterate entities -> create fbProc with IR -> lower to x86-64 machine code -> emit valid ELF .o file -> register with linker.

**Files created/modified:**
- `src/fb_ir.h` — Added `gb_resize_array` macro, `current_block`/`machine_code`/`machine_code_size`/`is_foreign`/`is_export` to `fbProc`, `fbLowCtx` struct, forward declarations for all new functions
- `src/fb_ir.cpp` — Instruction emission (`fb_inst_emit`, `fb_block_create`, `fb_block_start`, `fb_aux_push`), procedure lifecycle (`fb_proc_create`, `fb_proc_destroy`), name mangling (`fb_mangle_name`, `fb_get_entity_name`), object path (`fb_filepath_obj`), updated `fb_generate_code` orchestration
- `src/fb_build.cpp` (new) — Entity iteration using `min_dep_count`, creates fbProc per procedure, emits entry block with `FB_RET` for non-foreign procs, marks entry point as exported
- `src/fb_abi.cpp` (new) — Stub for future ABI classification
- `src/fb_lower_x64.cpp` (new) — x86-64 lowering: prologue (`push rbp; mov rbp,rsp`), `FB_RET` -> epilogue + ret, `FB_UNREACHABLE` -> ud2, `FB_TRAP`/`FB_DEBUGBREAK` -> int3, `fb_lower_all` orchestration
- `src/fb_emit_elf.cpp` (new) — Self-contained ELF64 writer (no system elf.h dependency), 9 sections (null, .text, .rodata, .data, .bss, .symtab, .strtab, .shstrtab, .rela.text), proper LOCAL/GLOBAL symbol ordering, `fb_emit_object` dispatch
- `src/main.cpp` — Added `#include` for all new files, added `linker_stage` dispatch in fast backend block

**What works:** `./odin build test.odin -file -fast` produces a valid ELF .o file. `objdump -d` shows correct `push rbp; mov rbp,rsp; mov rsp,rbp; pop rbp; ret` for all procedures. `readelf -a` shows valid ELF structure with proper section headers, symbol table (FUNC types, LOCAL/GLOBAL binding), file symbol, and foreign symbols as UNDEF. Linking fails as expected (no runtime implementation). LLVM backend is unaffected.

### Phase 3: Stack Frame & Integer Arithmetic (DONE)

Implemented stack frame layout, block-local register allocation, and instruction lowering for integer computation.

**Files modified:**
- `src/fb_ir.h` — Added `fbX64Reg` enum (RAX=0..R15=15), `fbRegState`, `fbStackLayout`, expanded `fbLowCtx` with GP register file, value location tracking, frame layout
- `src/fb_ir.cpp` — Added `fb_slot_create()` helper for stack slot allocation
- `src/fb_build.cpp` — Test IR: ALLOCA(8,8) + ICONST(42) + STORE + LOAD + ICONST(1) + ADD + RET
- `src/fb_lower_x64.cpp` — Complete rewrite with:
  - **Encoding helpers:** `fb_x64_rex`, `fb_x64_modrm`, `fb_x64_sib`, `fb_x64_imm8/32/64`, `fb_x64_modrm_rbp_disp32`, `fb_x64_modrm_indirect`, `fb_x64_mov_rr`, `fb_x64_mov_ri32`, `fb_x64_mov_ri64`
  - **Register allocator:** 9 caller-saved registers (RAX,RCX,RDX,RSI,RDI,R8-R11), LRU eviction with `u16 exclude_mask`, spill/reload, `fb_x64_alloc_gp`, `fb_x64_resolve_gp`, `fb_x64_spill_reg`, `fb_x64_find_lru`, `fb_x64_move_value_to_reg`
  - **Frame layout:** `fb_x64_compute_frame` (sort by alignment via index array, assign negative RBP offsets, spill area, 16-byte alignment)
  - **Prologue/epilogue:** `fb_x64_emit_prologue` (push rbp / mov rbp,rsp / sub rsp,N with imm8 for small frames), `fb_x64_emit_epilogue` (mov rsp,rbp / pop rbp / ret)
  - **Opcode lowering:** FB_ICONST (xor-zero/mov-ri32/mov-r32-imm32/movabs-ri64), FB_ALLOCA (lea [rbp+off]), FB_LOAD (movzx/mov by type, no unnecessary REX.W on movzx), FB_STORE (mov by type with proper prefix), FB_ADD/SUB/AND/OR/XOR (generic ALU helper with source protection), FB_MUL (IMUL), FB_NEG/NOT (F7 /3 /2), FB_SHL/LSHR/ASHR/ROL/ROR (CL shift via move_value_to_reg), FB_SDIV/UDIV/SMOD/UMOD (RAX:RDX division helper with proper value invalidation), FB_MEMBER (lea with disp32, large-offset protection), FB_ARRAY (SIB for 1/2/4/8 stride, imul+add with full register protection otherwise)

**What works:** `objdump -d` confirms correct instruction sequences: prologue with frame allocation (imm8 for ≤127 byte frames), ALLOCA→lea, ICONST→mov, STORE→mov [reg], LOAD→mov from [reg], ADD→mov+add, epilogue+ret. All existing fast backend tests pass.

### Phase 4: Control Flow & Comparisons (DONE)

Implemented multi-block control flow with forward branch patching, all integer comparisons, conditional select, and branch optimizations.

**Key implementation details:**
- `FB_CMP_*` → `CMP` + `SETcc` + `MOVZX` (mandatory REX prefix for byte-register operands to avoid legacy AH/CH/DH/BH encoding on registers 4-7)
- `FB_SELECT` → `TEST r8,r8` + `CMOVcc` (with mandatory REX for the TEST byte operand)
- `FB_BRANCH` → `TEST r8,r8` + `Jcc rel32` with fixup; identical-target optimization emits unconditional jump or fallthrough; three-way layout: false-fallthrough (jnz true), true-fallthrough (jz false), neither (jnz true + jmp false)
- `FB_JUMP` → `JMP rel32` with fixup; fallthrough elision when target is next block
- `FB_SWITCH` → linear scan: `CMP rkey, imm32` + `JE case_block` for each case, `JMP default_block` at end; default fallthrough elision
- Unified condition code helper `fb_x64_cmp_to_cc` returns raw x86 codes (0x4=E, 0x5=NE, etc.) reusable across SETcc, Jcc, and CMOVcc
- Block-boundary register spilling: `reset_regs` iterates allocatable registers and spills dirty values before clearing register state, ensuring `value_loc` consistency for cross-block control flow
- Branch fixup patching after all blocks emitted (all fixups are rel32); backward branches compute displacement immediately

### Phase 5: ABI & Function Calls (PARTIAL)

Implemented SysV AMD64 scalar ABI classification, parameter receiving, function calls with register/stack arguments, and relocation emission.

**Files created/modified:**
- `src/fb_abi.cpp` — SysV AMD64 type classification with struct/array decomposition (scalar, pointer, slice, string, dynamic array, map, enum, bit set; complex/quaternion explicitly MEMORY; small structs/arrays ≤16B with all-INTEGER fields recursively classified as 1×/2×INTEGER)
- `src/fb_ir.h` — Added `fbReloc`/`fbRelocType`, `fbParamLoc` struct (slot_idx + sub_offset), `param_locs`/`param_count` to `fbProc`
- `src/fb_build.cpp` — `fb_setup_params()` creates stack slots for GP register params: 8-byte for single-eightbyte, 16-byte for two-eightbyte (string, slice) with sub_offset tracking; Odin CC appends context pointer as last GP arg
- `src/fb_lower_x64.cpp` — `FB_SYMADDR` → `value_sym` tracking (deferred materialization via RIP-relative LEA); `FB_CALL` lowering: spill all caller-saved, push stack args in reverse, load register args into ABI-mandated registers, emit direct `CALL rel32` (with PLT32 reloc) or indirect `CALL r11`; prologue parameter spills; relocation accumulation
- `src/fb_emit_elf.cpp` — `.rela.text` emission with proper R_X86_64_PLT32 relocations

**What works:** Direct and indirect function calls with up to 6 GP register arguments + stack overflow arguments. Parameter receiving via prologue spills with sub-offset support for two-eightbyte params (string, slice share one 16-byte slot). PLT32 relocations for cross-procedure calls. Odin CC context parameter passing. Foreign procedure declarations skip heap allocations (no instruction/block/slot/aux/loc arrays allocated — significant since foreign procs often outnumber defined procs). Block tracking enforced via assertions (`fb_block_start` required before `fb_inst_emit`).

**Remaining:**
- Struct return via sret (hidden pointer)
- `FB_TAILCALL` lowering
- Win64 ABI classification

### Phase 6: Builder — Expressions & Statements (PARTIAL)

The largest phase. Implement the AST -> IR builder, mirroring `tilde_expr.cpp` + `tilde_stmt.cpp`.

**Phase 6a: AST Walker (DONE)**

Core AST-to-IR translation with expression, statement, and address builders.

**Files created/modified:**
- `src/fb_build.cpp` — Full rewrite from void-stub generator to AST walker (~1800 lines)
- `src/fb_ir.cpp` — `map_clear` on entity proc map for repeated calls, block tracking assertions
- `src/fb_lower_x64.cpp` — Added lowerers for FB_MEMZERO (rep stosb), FB_PTR2INT/FB_INT2PTR (trivial mov on x64), FB_FCONST, FBT_F32 in LOAD/STORE

**What works:**
- `fb_build_expr()` — integer/float/bool/nil literals, identifiers, binary ops (arithmetic, bitwise, comparison), unary ops (not, neg), casts, field access (`.member`), indexing (arrays, slices, dynamic arrays, strings), procedure calls, implicit context access
- `fb_build_stmt()` — assignments (=, +=, etc. with correct float opcode selection), if/else, for loops (with break/continue), switch statements, return (with defer emission), defer (three-mode algorithm: Default/Return/Branch), block scopes, labeled break/continue (with cross-scope defer emission)
- `fb_build_addr()` — Default (pointer), Context (implicit context field chains), partial SOA addressing
- `fb_emit_conv()` — int↔int (sext/zext/trunc), float↔float (fpext/fptrunc), int↔float, bool↔float, float→bool, ptr↔int conversions
- `fb_type_is_signed()` — correctly returns false for pointers, bitsets, and non-integer types (unsigned by default)
- Variable → stack slot mapping via `fb_add_local()`
- Context parameter handling (Odin CC appends context pointer)
- Defer execution: LIFO deferred statement emission at scope close (Default), return (Return — all scopes), and break/continue (Branch — scopes above target). `fbTargetList` carries `scope_index` for cross-scope defer resolution
- Multi-return explicitly guarded with `GB_ASSERT_MSG` (both Odin CC and non-Odin CC call paths)
- Compound literals (`Ast_CompoundLit`) — struct (named/positional fields), fixed-size array, nested struct, enumerated array
- CmpAnd/CmpOr lowered correctly using temp alloca (not cross-block SELECT)
- Runtime stubs: `__$startup_runtime` and `__$cleanup_runtime` synthesized as `ret` stubs
- `EntityFlag_CustomLinkage_Strong` respected for proper global symbol visibility
- Foreign library enumeration into `LinkerData` for system library linking

**Remaining:**
- Full struct/union field access patterns
- Complex address kinds: Map, SOA (full), RelativePtr, Swizzle, BitField
- Constant folding in the builder
- Type switches
- Inline assembly

**Phase 6b: Built-in Procedures & Float Fix (DONE)**

Built-in procedure dispatch and float opcode correction.

**Files created/modified:**
- `src/fb_build_builtin.cpp` — New file (~340 lines), complete builtin dispatch
- `src/fb_build.cpp` — Ast_CallExpr now detects `Addressing_Type` (type conversions) and `Addressing_Builtin` (builtins); float arithmetic/comparison/negation now select correct FB_FADD/FSUB/FMUL/FDIV and FB_CMP_FEQ/FNE/FLT/FLE/FGT/FGE opcodes
- `src/fb_lower_x64.cpp` — MEMZERO reads size from value register (not imm); added FB_MEMCPY lowering (rep movsb)
- `src/fb_ir.h` — Forward declaration for `fb_build_builtin_proc()`

**What works:**
- Container builtins: `len`, `cap`, `raw_data` for slices, strings, dynamic arrays (field offsets use `ptr_size`: data@0, len@ptr_size, cap@ptr_size+int_size)
- Arithmetic builtins: `min` (variadic fold-left with CMP+SELECT), `max`, `abs` (NEG+CMP+SELECT), `clamp` (max then min)
- Pointer builtins: `ptr_offset` (ARRAY opcode), `ptr_sub` (PTR2INT, SUB, SDIV)
- Memory builtins: `mem_copy` (MEMCPY → rep movsb), `mem_zero` (MEMZERO → rep stosb)
- Bit manipulation: `byte_swap` (BSWAP), `count_ones` (POPCNT), `count_zeros` (NOT+POPCNT), `count_leading_zeros` (CLZ), `count_trailing_zeros` (CTZ)
- Misc: `trap`/`debug_trap`/`unreachable`, `expect` (passthrough), `read_cycle_counter` (CYCLE), `cpu_relax` (no-op)
- Float arithmetic uses correct SSE opcodes in both binary expressions and compound assignments (`+=`, `-=`, `*=`, `/=`)
- Type conversion via call syntax (`int(x)`, `f32(y)`) now handled
- x64 lowering: unimplemented opcodes produce categorized `GB_PANIC` messages (float arithmetic, float comparison, float conversion, atomics, wide arithmetic, bit manipulation, SIMD, miscellaneous) instead of silent `ud2` traps
- `fb_x64_resolve_gp` asserts when a value has no location and no symbol reference, catching dangling value references early

**Phase 6c: Compound Literals & Entry Point (DONE)**

Struct, array, and nested struct compound literal initialization. Entry point now builds full user code from AST instead of synthetic stub IR.

**Files created/modified:**
- `src/fb_build.cpp` — `fb_build_compound_lit()` dispatch, `fb_build_compound_lit_struct()` (named and positional fields via `lookup_field`/`lookup_field_from_index`), `fb_build_compound_lit_array()` (positional, indexed, range init), `fb_build_compound_lit_enumerated_array()`, `fb_emit_copy_value()` helper (scalar STORE vs aggregate MEMCPY dispatch); entry point injects `__$startup_runtime` call before body; C `main` bridge calls user's entry point with null context
- `src/fb_lower_x64.cpp` — Fixed MEMCPY/MEMZERO register tracking: `fb_x64_spill_reg()` after `move_value_to_reg()` but before `rep` instruction ensures `value_loc[]` consistency when physical registers are clobbered
- `src/fb_ir.h` — `startup_proc_idx` and `entry_proc_idx` fields on `fbModule`

**What works:**
- Struct compound literals with named fields (`Vec2{x = 10, y = 20}`) — uses `lookup_field()` for deep selection path walking (embedded/using fields)
- Struct compound literals with positional fields (`Vec2{3, 7}`) — uses `lookup_field_from_index()` via `st->fields[index]->Variable.field_index`
- Empty struct literals (`Vec2{}`) — zero-initialized via MEMZERO
- Partial initialization (`Vec2{x = 42}`) — MEMZERO + store only named fields, remaining fields stay zero
- Fixed-size array literals (`[3]int{10, 20, 30}`) — MEMZERO + per-element STORE at computed offsets
- Nested struct literals (`Rect{min = Vec2{1,2}, max = Vec2{3,4}}`) — recursive compound literal build, inner results MEMCPY'd into outer aggregate
- Struct reassignment with compound literals — aggregate MEMCPY from temp to destination
- Enumerated array literals — index offset from `bt->EnumeratedArray.min_value`
- All aggregate initialization uses alloca + MEMZERO + per-field STORE + MEMCPY-to-destination pattern
- Entry point builds full AST body (no longer synthetic stub), with startup call injected
- C `main` (runtime bridge) properly calls user's entry point, returns 0
- MEMCPY/MEMZERO register clobbering no longer causes stale `value_loc[]` entries

**Pattern: Aggregate value flow at -O0.**
- `fb_data_type(type).kind == FBT_VOID` identifies aggregates (structs, arrays, unions)
- Compound literal → alloca temp, zero-init, fill fields, return pointer
- `fb_build_expr(Ast_CompoundLit)` returns pointer tagged with aggregate type
- Assignment/init: callers check `FBT_VOID` → use `fb_emit_copy_value()` (MEMCPY) instead of STORE
- This convention avoids introducing aggregate types into the scalar IR

**Not yet supported:** Slice literals (`[]int{1,2,3}` — requires runtime allocation), dynamic array literals, map literals, bit_set literals, union literals

**Phase 6d: Float/XMM Lowering & Bug Fixes (DONE)**

Implemented x64 lowering for all 25 float and bit manipulation opcodes that were previously `GB_PANIC` stubs, plus critical bug fixes in ABI classification, shift register tracking, and bool conversion ordering.

**Files modified:**
- `src/fb_lower_x64.cpp` — XMM encoding helpers (`fb_x64_movd_gp_to_xmm`, `fb_x64_movq_gp_to_xmm`, `fb_x64_gp_to_xmm`, etc.), `fb_x64_float_binop` template, `fb_x64_float_cmp_nan_safe` helper, lowering for 25 opcodes (9 float arith + 6 float cmp + 6 float conv + 4 bit manip); shift helper (`fb_x64_shift_cl`) now spills RCX correctly after use
- `src/fb_build.cpp` — Bool conversion paths moved before general integer/float paths in `fb_emit_conv`; `fb_emit_cmp` stores source type in `imm` for float comparisons (`ucomiss` vs `ucomisd` selection); SSE-classified parameters allocated as GP slots in `fb_setup_params`
- `src/fb_abi.cpp` — `Basic_any` (`{rawptr, typeid}` = 16 bytes) correctly classified as 2×INTEGER instead of 1×INTEGER

**What works:**
- Float arithmetic: FADD, FSUB, FMUL, FDIV, FMIN, FMAX (SSE scalar via XMM0/XMM1 scratch)
- Float unary: FNEG (XOR sign bit in GP), FABS (AND mask in GP), SQRT (SQRTSS/SQRTSD)
- Float comparison: all 6 FP comparisons with NaN-safe patterns (see §11.7)
- Float conversion: SI2FP with sign-extension fix for sub-i32 sources, UI2FP (full u64 range via halving trick), FP2SI, FP2UI (full u64 range via conditional subtraction), FPEXT, FPTRUNC
- Bit manipulation: BSWAP, POPCNT, CLZ (BSR+XOR), CTZ (BSF)
- `any` type parameters correctly use 2 GP registers (was broken: 16 bytes misclassified as single-eightbyte)
- Shift instructions no longer corrupt `value_loc[]` tracking — RCX is properly spilled after the shift, not just cleared
- Bool→int uses ZEXT (not SEXT); int→bool uses CMP_NE against 0 (not TRUNC); bool→float uses UI2FP (not SI2FP); float→bool uses CMP_FNE against 0.0 (not FP2SI). These paths precede general integer/float conversion to prevent FBT_I1 from being caught by the wider `fb_type_is_integer()` predicate

**Bug fixes consolidated:**
- Shift spill: `fb_x64_shift_cl` replaces manual `gp[RCX].vreg = FB_NOREG` with `fb_x64_spill_reg` so `value_loc` stays consistent
- `any` ABI: `Basic_any` size is 16 bytes (`{rawptr, typeid}`), not 8 — classified as 2×INTEGER for two-register passing
- Bool conversion ordering: FBT_I1 ∈ `fb_type_is_integer()` was shadowing bool-specific ZEXT/compare semantics with incorrect SEXT/truncate
- SI2FP sign-extension: `LOAD` uses `MOVZX` (zero-extension) for i8/i16, so `cvtsi2ss` needs explicit `MOVSX` first to get correct negative values

**Phase 6e: Multi-Return & Context Fix (DONE)**

Implemented Odin calling convention multi-return support and fixed a pre-existing context parameter passing bug.

**Multi-return convention:**
- Return values 0..N-2 are passed via hidden output pointer parameters
- Return value N-1 is returned in a register (RAX for integers, XMM0 for floats)
- Parameter order: [sret] [regular params] [split return ptrs] [context]
- Split return pointers are caller-allocated stack temporaries; callee stores through them

**Files modified:**
- `src/fb_ir.h` — Added `split_returns_index` and `split_returns_count` to `fbProc` for tracking hidden output pointer param slots; added `last_call_split_temps` and `last_call_split_count` to `fbBuilder` for communicating split return addresses from call builder to statement-level unpacking
- `src/fb_ir.cpp` — Initialize `split_returns_index = -1` in `fb_proc_create`
- `src/fb_build.cpp` — `fb_setup_params` creates split return pointer param slots between regular params and context; `fb_build_call_expr` allocates stack temps, passes hidden output pointers, returns last value; `fb_unpack_multi_return` helper loads values from split temps; `fb_build_return_stmt` stores first N-1 values through hidden output pointers, RETs last value; `fb_build_mutable_value_decl` and `fb_build_assign_stmt` detect multi-return calls (single RHS with Tuple type, multiple LHS names) and unpack via `fb_unpack_multi_return`

**What works:**
- Two-return functions: `proc() -> (int, bool)`, `proc() -> (bool, int)`
- Three-return functions: `proc() -> (int, int, bool)`
- Chained multi-return calls (result of one feeds another)
- Reassignment with multi-return: `a, b = f()`
- Blank identifiers in multi-return: `_, ok := f()`, `q, _ := f()`, `_, _, ok := f()`
- Error-path returns (early returns with different values)

**Bug fix — context parameter passing:**
- The context pointer was passed as the ALLOCA address (pointer to stack slot) instead of the loaded pointer value. Changed to `fb_addr_load` the context slot before pushing to aux pool. This was a pre-existing bug that happened to work accidentally when the callee didn't dereference the context deeply.

**Phase 6f: Range Statements / For-In Loops (DONE)**

Added `Ast_RangeStmt` support covering integer range intervals and indexed collection iteration.

**Files modified:** `src/fb_build.cpp` (added ~300 lines)

**New functions:**
- `fb_strip_and_prefix` — strips unary `&` prefix from range variable identifiers
- `fb_build_range_interval` — handles `for val, idx in lo..<hi` / `lo..=hi` / `lo..hi`
- `fb_build_range_indexed` — handles `for val, idx in array / slice / dynamic_array`
- `fb_build_range_stmt` — main dispatch, wired into `fb_build_stmt` as `Ast_RangeStmt` case

**Integer range interval block structure:**
```
[entry] store lo → value_slot, store upper → upper_slot, jump → loop
[loop]  load value, load upper, cmp (< or <=), branch → body/done
[body]  user code, jump → check (inclusive) or post (exclusive)
[check] reload value != upper? → post/done  (wrapping guard for inclusive)
[post]  increment value (and index), jump → loop
[done]  scope close
```

The wrapping guard prevents infinite loops when upper equals the type's maximum value on inclusive ranges. Upper bound is stored in a local to survive across blocks in the block-local register allocator.

**Indexed range block structure (forward):**
```
[entry] store -1 → index, jump → loop
[loop]  index += 1, cmp index < count, branch → body/done
[body]  val = collection[index], user code, jump → loop
[done]  scope close
```

**Indexed range (reverse):**
```
[entry] store count → index, jump → loop
[loop]  index -= 1, cmp index < 0, branch → done/body
[body]  val = collection[index], user code, jump → loop
[done]  scope close
```

**Supported iteration types:**
- Integer ranges: `..<` (exclusive), `..=` (inclusive), `..` (inclusive)
- Float ranges: `..<`, `..=`, `..` (uses `FADD` with proper `FCONST 1.0` step)
- Fixed-size arrays (`[N]T`)
- Slices (`[]T`)
- Dynamic arrays (`[dynamic]T`)
- `#reverse` for all indexed types

**Not yet supported:** maps, strings, enums, bitsets, enumerated arrays, SoA structs, tuples.

**What works (46+ checks across 3 test files):**
- Basic exclusive and inclusive integer ranges with correct bounds
- Range with value and index bindings
- Single-element inclusive range (wrapping guard)
- Negative integer ranges
- Blank identifier bindings (`_`)
- Array, slice, dynamic array iteration
- Nested ranges (including range × array)
- `break` and `continue` (unlabeled)
- Labeled `break outer` and `continue outer` across nested ranges
- `#reverse` array iteration with correct ordering
- Subslice iteration
- Ranges inside called procedures with early return
- Complex loop bodies with multiple locals
- Dot product via indexed range over slices

**Phase 6g: Correctness Fixes — Division, Dirty Tracking, Container Offsets, Bool (DONE)**

Bug fixes across lowering, builtins, and the builder discovered via test programs.

**Files modified:**
- `src/fb_lower_x64.cpp` — Division spill fix, dirty tracking fix in `move_value_to_reg`
- `src/fb_build_builtin.cpp` — Container field offset fix (all `len`/`cap` loads)
- `src/fb_build.cpp` — Float range step, bool signedness

**Bug fixes:**
- **Division spill:** `fb_x64_div` now flushes the dividend to its spill slot *before* DIV clobbers RAX, then detaches the value from RAX (`value_loc[a] = spill_offset, gp[RAX].vreg = FB_NOREG`). Previously, `move_value_to_reg` put the dividend in RAX but DIV overwrote it, leaving `value_loc` pointing at an unwritten spill slot — any later reload would read garbage
- **Dirty tracking:** `fb_x64_move_value_to_reg` now marks values as dirty when `loc >= 0` (register) *or* `loc == FB_LOC_NONE` (freshly materialized, e.g. SYMADDR via LEA). Only spill-slot reloads (`loc < 0 && loc != FB_LOC_NONE`) are clean. Previously, SYMADDR-materialized values were marked clean, so eviction skipped the store and reloads read uninitialized stack memory
- **Container offsets:** `len` field offset changed from `int_size` to `ptr_size` throughout `fb_builtin_len`, `fb_builtin_cap`, and `fb_build_range_indexed`. On 64-bit targets these are identical (both 8), but the correct semantic is that `len` follows the data pointer (`rawptr`), not a preceding integer. `cap` offset changed from `2 * int_size` to `ptr_size + int_size`
- **Bool signedness:** `fb_type_is_signed` now returns `false` for `BasicFlag_Boolean` types before checking `BasicFlag_Unsigned`. Booleans are logically unsigned — without this, `bool` (which lacks `BasicFlag_Unsigned`) was treated as signed, causing SEXT instead of ZEXT in widening conversions
- **Float range step:** `fb_build_range_interval` now uses `fb_emit_fconst(b, iter_type, 1.0)` instead of `fb_emit_iconst(b, iter_type, 1)` for float ranges. The integer bit pattern `0x1` is not `1.0` in IEEE 754 — the increment was producing a subnormal (~1.4e-45 for f32) instead of 1.0

**Phase 6h: Block-boundary Register Spill Fix (DONE)**

Fixed a critical register allocator bug: spill code was emitted at the start of each basic block, shaped for the *previous* block's register state. When control arrived from a different predecessor, the spill wrote physical registers to wrong spill slots, causing SIGSEGV.

**Files modified:**
- `src/fb_lower_x64.cpp` — Added `fb_x64_clear_reg_state()` (clears register bookkeeping without emitting code) and `fb_x64_is_terminator()`. Changed main lowering loop: `clear_reg_state` at block start (no code emission), `reset_regs` before each terminator (emits spill code on the correct control flow path).

**Phase 6i: String Constants & .rodata (DONE)**

String literal support: `.rodata` ELF section, string interning, ABI decomposition for 2-eightbyte types.

**Files modified:**
- `src/fb_ir.h` — Added `fbRodataEntry` struct, `rodata_entries` and `string_intern_map` on `fbModule`
- `src/fb_ir.cpp` — Added `fb_module_intern_string_data()` for string deduplication; init/destroy for new fields
- `src/fb_build.cpp` — `ExactValue_String` handler in `fb_const_value` (builds string struct on stack from rodata pointer + length); ABI decomposition in `fb_build_call_expr` for 2-eightbyte INTEGER types (string, slice, any); `fb_addr_load` returns pointer for aggregate types (FBT_VOID) instead of scalar load
- `src/fb_emit_elf.cpp` — Added `.rodata` section (FB_ELF_SEC_RODATA=2), `STT_OBJECT` symbol type, unified `sym_elf_idx[]` array covering both proc and rodata symbols, rodata symbols emitted as `STB_LOCAL, STT_OBJECT`

**What works:**
- String literals: length, comparison, passing to functions
- Automatic interning: identical string constants share one rodata entry
- cstring support via `FB_SYMADDR` pointing directly at rodata
- 2-eightbyte ABI: string/slice/any arguments decomposed into two register-sized values at call sites

**Phase 6j: Switch Statements (DONE)**

Full switch statement support with two dispatch strategies and fallthrough.

**Files modified:**
- `src/fb_build.cpp` — Added `fb_switch_can_be_trivial()` (checks for all-constant integer cases, no ranges) and `fb_build_switch_stmt()` (~120 lines); added `Ast_SwitchStmt` case in `fb_build_stmt`; added `Token_fallthrough` handling in `BranchStmt`

**What works:**
- **Trivial path** (FB_SWITCH IR instruction): constant integer/bool/enum cases → single SWITCH instruction → lowered to CMP+JE chain in x86-64
- **Non-trivial path** (chain of CMP+BRANCH): tag-less boolean switches, range cases (`..`, `..=`, `..<`), non-constant case values
- Multiple values per case (`case 1, 2, 3:`)
- Default case (any position, not just last)
- Tag-less switch (`switch { case x < 10: ... }` → implicit `switch true`)
- Init statements (`switch x := 5; x { ... }`)
- Fallthrough (`fallthrough` → jumps to next case body)
- Fallthrough chains (multiple consecutive fallthroughs)
- Labeled break out of switch
- Nested switches, switches in loops
- Return from within switch cases
- Scope/defer management per case clause

**Phase 6k: String Indexing, Slice Expressions, or_else (DONE)**

Incremental feature additions that unlock more of the standard library.

**Files modified:**
- `src/fb_build.cpp` — Added string case to `IndexExpr` in `fb_build_addr` (loads `.data` pointer before indexing); added `Ast_SliceExpr` handler in `fb_build_addr` (array/slice/string/dynamic array → `{data+lo*stride, hi-lo}` local); moved `fb_load_field` from `fb_build_builtin.cpp` (shared helper); added `Ast_OrElseExpr` and `Ast_OrReturnExpr` in `fb_build_expr` (multi-return unpack → branch on ok → temp local merge)
- `src/fb_build_builtin.cpp` — Removed `fb_load_field` definition (now in `fb_build.cpp`)

**What works:**
- String indexing (`s[i]` loads byte from string data pointer)
- Array slicing (`arr[lo:hi]`, `arr[:]`, `arr[lo:]`, `arr[:hi]`)
- Slice-of-slice (`s1[lo:hi]`)
- String slicing (`s[lo:hi]`)
- Dynamic array slicing
- `or_else` with multi-return `(value, ok)` procedures
- `or_return` with multi-return `(value, ok)` procedures
- Chained `or_else`, `or_else` in loops, `or_else` with call fallbacks

**Phase 6l: Aux Pool Interleaving Fix (DONE)**

Fixed a critical call codegen bug: when a call argument contains a nested call (e.g. `check(get_zero() == 0, 1)`), the inner call's aux entries were included in the outer call's argument range. This shifted all arguments by one — the inner call's context pointer became the outer call's first argument.

**Root cause:** `aux_start` was captured before evaluating argument expressions. Nested `fb_build_call_expr` invocations pushed their own aux entries (context pointer, split return pointers) into the shared aux pool between `aux_start` and the outer call's actual arguments.

**Fix:** Two-phase argument building in `fb_build_call_expr`: (1) evaluate all argument expressions first (may trigger nested calls), (2) capture `aux_start` and push this call's arguments. This ensures nested call aux entries live outside the outer call's `[aux_start, aux_start+arg_count)` range.

**Files modified:**
- `src/fb_build.cpp` — Restructured `fb_build_call_expr` argument building into evaluate-then-push phases
- `tests/fast_backend/test_all.odin` — Unified test suite; reverted manual inline workarounds to use `check()` directly

**Phase 6m: Global Variables (DONE)**

Package-level variable support: discovery, constant serialization, and ELF `.data`/`.bss` emission.

**Files modified:**
- `src/fb_ir.h` — Added `FB_GLOBAL_SYM_BASE` constant (0x40000000), `fbGlobalEntry` struct, `global_entries`/`global_entity_map` fields to `fbModule`
- `src/fb_ir.cpp` — Init/destroy for global_entries and global_entity_map in module lifecycle
- `src/fb_build.cpp` — `fb_generate_globals()` discovers file-scope variables from `variable_init_order`, serializes constant initializers (bool, int, float, pointer) via `fb_serialize_const_value()`; `fb_make_global_addr()` helper for global address construction; global lookup in `fb_build_addr` and `fb_build_expr` via `FB_GLOBAL_SYM_BASE + gidx`
- `src/fb_emit_elf.cpp` — `.data` section (SHT_PROGBITS, SHF_WRITE|SHF_ALLOC) for constant-initialized globals, `.bss` section (SHT_NOBITS) for zero-initialized globals; `sh_addralign` computed from max entry alignment; separate `global_sym_elf_idx` array for relocation dispatch; `FB_GLOBAL_SYM_BASE` check in relocation loop
- `src/fb_lower_x64.cpp` — No changes needed (globals flow through existing SYMADDR/reloc path)
- `tests/fast_backend/test_all.odin` — Tests 950-959: zero-init, const-init (int/f64/bool), mutation, cross-function read/write

**What works:**
- Zero-initialized globals (`.bss`)
- Constant-initialized globals with bool, integer, float, pointer values (`.data`)
- Reading and writing globals from any procedure in the package
- Cross-function global mutation (write in one proc, read in another)
- Proper ELF symbol types (`STT_OBJECT`, correct section/offset/size)
- Foreign global variable declarations (`SHN_UNDEF`)

**Known limitations:**
- Non-trivial initializers (strings, compound literals) fall back to zero-init until `__$startup_runtime` runs proper init code
- No `.rela.data` for globals whose initializers reference other symbols

**Phase 6n: Expression Completions (DONE)**

Four missing expression kinds that blocked significant code patterns.

**Files modified:**
- `src/fb_build.cpp` — Added `Ast_TernaryIfExpr`, `Ast_TernaryWhenExpr`, `Ast_ImplicitSelectorExpr`, `Ast_SelectorCallExpr` cases in `fb_build_expr`
- `tests/fast_backend/test_all.odin` — Tests 1000-1031: ternary if (trivial SELECT and general branch paths), implicit selectors (enum values, comparisons, switch dispatch), selector calls, ternary when (compile-time), combined patterns (ternary in loops, as function arguments, multiple in one expression)

**What works:**
- **Ternary if** (`x if cond else y`): two-path implementation. Scalar types with trivial arms (constants, identifiers, simple selectors) use `FB_SELECT` — no control flow, single instruction. General case uses branch + temp alloca merge (same pattern as CmpAnd/CmpOr). Aggregate types (structs, arrays) use `fb_emit_copy_value` through the branch path. Nested ternaries work correctly
- **Ternary when** (`x when COND else y`): compile-time conditional. The condition is evaluated at compile time (ExactValue_Bool). Only the chosen arm is emitted — no dead code
- **Implicit selectors** (`.Field_Name`): pure constant emission. The checker resolves these to `Addressing_Constant` with the enum/union value. Just delegates to `fb_const_value`
- **Selector calls** (`obj.method(args)`): the checker rewrites these into regular calls (`se->modified_call`). Forwards to `fb_build_expr(b, se->call)`

**Design note — trivial arm detection for SELECT:**
The ternary if uses a `is_trivial` lambda matching the LLVM backend's heuristic: constants, bare identifiers, one-level selector expressions on identifiers, and non-address-of unary expressions on trivial operands are considered side-effect-free. When both arms are trivial AND the result type is scalar, both are evaluated eagerly and combined with SELECT — avoiding 3 basic blocks per ternary. This matters for idiomatic patterns like `x if flag else y` in hot loops.

**Correctness details:**
- The general branch path guards both `fb_emit_jump` calls with `fb_block_is_terminated` checks, following the codebase convention. This prevents double-termination if arm evaluation ever terminates a block (e.g., future noreturn call support)
- `TernaryWhenExpr` asserts `Addressing_Constant` on the condition, matching the LLVM backend — the checker guarantees this but the assertion catches internal errors early

**Phase 6o: Union Types, Type Assertions, MEMORY-Class Params (DONE)**

Implemented tagged union support, type assertion expressions, and MEMORY-class aggregate parameter passing.

**Files modified:**
- `src/fb_build.cpp` — `fb_emit_store_union_variant()` (writes data + tag, handles maybe-pointer, zero-sized variants, memzero of stale data); `fb_emit_conv()` gained union conversion path (value→union via temp alloca); `fb_build_compound_lit()` added `Type_Union` case; two separate type assertion paths: address-of (`&v.(T)`) and value (`v.(T)`), each handling both tuple `(T, bool)` and direct `T` forms with trap-on-mismatch; `fb_build_mutable_value_decl`/`fb_build_assign_stmt` extended to handle aggregate tuple pointers from type assertions (distinct from split-return temps)
- `src/fb_build.cpp` — MEMORY-class parameters: `fb_setup_params` allocates GP register slots for hidden pointers; procedure begin dereferences MEMORY param pointers via `fb_emit_load`
- `src/fb_ir.h` — No new types (reuses existing structures)
- `tests/fast_backend/test_union.odin` — 82 lines of union tests

**What works:**
- Tagged union creation from compound literals (`Value{i = 42}`)
- Implicit union conversion in assignment and call arguments
- Maybe-pointer unions (tag-free, nil = no value)
- Zero-sized variant handling (memzero stale data region)
- Type assertion with tuple return: `val, ok := u.(int)`
- Type assertion with direct return: `val := u.(int)` (traps on mismatch)
- Address-of type assertion: `ptr, ok := &u.(int)`; `ptr := &u.(int)` (traps on mismatch)
- MEMORY-class aggregate parameters (>16 bytes) passed as hidden pointers in GP registers

**Phase 6p: C Interop ABI — XMM Parameters, Small Structs, Unsigned Float Conversions (DONE)**

Full SysV AMD64 ABI compliance for C interop: XMM float parameter passing/receiving, small struct decomposition, and correct unsigned-to-float/float-to-unsigned conversions for the full u64 range.

**Files modified:**
- `src/fb_abi.cpp` — Recursive struct/array ABI decomposition: structs ≤16B with all-INTEGER fields classified as 1×/2×INTEGER; small arrays ≤16B similarly decomposed; packed/raw_union structs conservatively go to MEMORY
- `src/fb_build.cpp` — `fb_setup_params` routes SSE-classified params to `fbXmmParamLoc` slots for non-Odin CC (XMM0-7); `xmm_param_locs`/`xmm_param_count` stored on fbProc; call codegen tracks `sse_mask`/`f64_mask` bitmasks in CALL instruction `imm` field; small struct arguments (≤8B, 1×INTEGER) loaded as scalar before passing
- `src/fb_lower_x64.cpp` — Prologue emits `movss`/`movsd` from XMM registers to stack slots; call lowering rewritten for mixed GP/XMM: independent GP and XMM register counting, SSE arg bitmask decoding, GP→XMM transfer via `movd`/`movq`; non-Odin CC SSE return capture from XMM0→GP; `UI2FP` halving trick for full u64 range; `FP2UI` conditional subtraction for full u64 range

**What works:**
- External C functions receiving float parameters in XMM0-XMM7
- Mixed integer/float parameter lists with correct register assignment
- SSE return value capture (f32/f64 from XMM0)
- Small struct arguments (≤8 bytes) passed as register-width integers
- `UI2FP` handles values ≥ 2^63 correctly (halving trick)
- `FP2UI` handles values ≥ 2^63 correctly (conditional subtraction)

**Phase 6q: Type Switch Statements (DONE)**

Union type switches (`switch v in union_val { case T: ... }`), the primary pattern for dispatching on union variants in Odin. Builds on the regular switch infrastructure (block allocation, comparison chain, scope/defer management, label handling) and the type assertion code (tag reading, variant index computation, data extraction).

**Files modified:**
- `src/fb_build.cpp` — `fb_build_type_switch_stmt()` implements the full type switch: scope setup, union pointer extraction, tag preloading (regular tag load, maybe-pointer nil comparison, zero-sized union), comparison chain dispatch (one CMP+BRANCH per case type), implicit entity binding (by-value: local copy, by-reference: retyped pointer), case body emission with target list for break. Dispatched from `fb_build_stmt` via `Ast_TypeSwitchStmt` case.

**What works:**
- Basic variant dispatch (int, f64, bool, struct variants)
- Default case (unmatched variant or nil union)
- Maybe-pointer unions (nil vs non-nil dispatch)
- By-value binding (copy to local, immune to union mutation)
- By-reference binding (pointer to union data, mutations visible)
- `#partial` switch (subset of variants)
- Labeled break
- Struct variant field access (read and write through by-ref)
- Type switch in functions (passing unions as parameters)
- Type switch in loops
- Return from within type switch case

**Deferred:**
- `any` type switches — requires runtime type info generation (Phase 7); asserts with clear message

### Phase 7: Remaining Odin Features (in progress)

**Phase 7a: `any` type construction + narrow-type fix** ✅

`any` boxing (`fb_emit_conv` in `fb_build.cpp`):
- `any` is `{data: rawptr, id: typeid}` — 16-byte aggregate, classified as FBT_VOID
- Boxing: allocate local, store value, compute `type_hash_canonical_type()` at compile time, store data pointer and typeid
- Handles scalars (alloc temp, store, take address) and aggregates (already pointers in IR)
- Handles `untyped_nil`/`untyped_uninit` → zero-initialized any

Selector expression fix (`fb_build_addr`, SelectorExpr):
- Replaced struct-only field walking with general `type_offset_of()` from `types.cpp`
- Now correctly handles field access on all aggregate-like types: `any`, `string`, `slice`, `dynamic_array`, `struct`, `tuple`, `union`

Signed narrow-type ICONST fix (`fb_emit_iconst`):
- **Root cause:** LOAD uses MOVZX (zero-extension is canonical form for sub-64-bit values), but ICONST stored sign-extended 64-bit values. Negative i8/i16/i32 constants had different 64-bit representations than loaded values.
- **Fix:** Mask ICONST immediates to type width via unsigned cast: `val = (i64)(u8/u16/u32)val`. Both LOADs and ICONSTs now produce identical zero-extended 64-bit representations.
- **Invariant:** All sub-64-bit integer values in registers are zero-extended. SEXT/ZEXT/TRUNC/STORE all read only the low bits, so this is safe.

**Narrow-type signed ordering comparisons (DONE):**
- **Problem:** CMP always used REX.W (64-bit), but signed comparisons on zero-extended narrow values give wrong results. E.g., `i8(-1)` = 0xFF zero-extended = 255; 64-bit signed CMP says 255 > 1, but i8(-1) < i8(1).
- **Fix:** `fb_emit_cmp` now stores packed operand type in `imm` for signed comparisons (FB_CMP_SLT through FB_CMP_SGE), same pattern already used for float comparisons. The x86-64 lowerer decodes the type and emits type-width CMP: 8-bit (`0x38`), 16-bit (`0x66 0x39`), 32-bit (`0x39`), 64-bit (`REX.W 0x39`).
- **EQ/NE and unsigned comparisons remain 64-bit** — correct because zero-extended values have identical bit patterns for equality and unsigned ordering.

**Remaining:**

- Map operations (runtime calls)
- SOA addressing
- Slice operations (`append`, `delete`, `make`, `new`)
- Dynamic array operations
- Bit fields, swizzle
- `any` type switches (requires runtime type info)
- Runtime type info generation
- SIMD builtins, atomic builtins

### Phase 8: SIMD, Atomics (TODO)

- SIMD vector operations (lane-wise arithmetic, shuffles, extracts/inserts)
- Atomic operations lowering to `lock` prefix / `cmpxchg`
- Memory fences
- Complex/quaternion type support

### Phase 9: Debug Info (TODO)

- DWARF generation for Linux/macOS
- `DW_TAG_subprogram` per function
- `DW_TAG_variable` with `DW_OP_fbreg` locations
- Line number program from `fbLoc` table
- Type DIEs from Odin `Type*`
- Lexical block scopes

### Phase 10: Object Format Completion (PARTIAL)

**ELF improvements (DONE):**
- `.rela.text` emission with proper R_X86_64_PLT32 relocations for cross-procedure calls
- Single-pass symbol table algorithm (count → allocate → populate with dual LOCAL/GLOBAL cursors)
- Batched padding writes (64-byte chunks instead of byte-at-a-time)
- `fb_buf_append_odin_str()` eliminates per-symbol C-string alloc/copy/free
- `fb_buf_align()` uses single `memset` instead of loop
- Self-contained ELF64 definitions with `static_assert` size checks
- `.data` and `.bss` sections for global variables (dynamic `sh_addralign` from max entry alignment)

**Remaining:**
- PE/COFF emission for Windows (`fb_emit_pe.cpp`)
- Mach-O emission for macOS (`fb_emit_macho.cpp`)
- CodeView debug info for Windows
- `.rela.data` relocations (for globals with symbol-reference initializers)

### Phase 11: Threading & Performance (TODO)

- Per-procedure arena allocation (replace `heap_allocator()` with arena — see §13)
- Parallel procedure building (thread pool)
- Parallel lowering
- Arena-per-procedure lifecycle (build → lower → free)
- Profile-guided allocation sizing (tune default array capacities)
