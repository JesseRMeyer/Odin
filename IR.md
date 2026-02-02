# IR Generation Improvement Plan

Analysis of LLVM IR generation in the Odin compiler, covering debug mode
performance, optimization metadata, and information provided to LLVM.

**LLVM version:** 20.1.0 (new pass system via `LLVMRunPasses`)
**Key files:**
- `src/llvm_backend_passes.cpp` — pass pipeline strings per opt level
- `src/llvm_backend_opt.cpp` — legacy pass manager (dead on LLVM 17+), custom passes
- `src/llvm_backend_debug.cpp` — debug info emission
- `src/llvm_backend_general.cpp` — loads, stores, GEPs, TBAA, control flow
- `src/llvm_backend_proc.cpp` — procedure codegen, calling conventions, attributes
- `src/llvm_backend_expr.cpp` — expression codegen, arithmetic
- `src/llvm_backend.hpp` — constants, configuration

---

## 1. Debug Mode Performance

### 1.1 No passes run at -opt:0 / debug

In `llvm_backend_passes.cpp:1-7`, the debug (`-1`) and O0 cases emit:

```
case -1:  "function(annotation-remarks)"
case 0:   "always-inline", "function(annotation-remarks)"
```

No mem2reg, no memcpyopt, no dead store elimination, no CFG simplification.
Every local variable remains as an alloca with explicit load/store pairs.
This is the primary cause of debug build slowness.

The legacy pass manager functions (`lb_populate_function_pass_manager` etc.)
are all guarded by `#if !LB_USE_NEW_PASS_SYSTEM` and are no-ops on LLVM 17+.

### 1.2 Why passes were removed: debug info model

The compiler uses **only `llvm.dbg.declare`** tied to allocas
(`llvm_backend_debug.cpp:1185-1187`). It never emits `llvm.dbg.value`.

`llvm.dbg.declare` says: "this variable lives at this stack address for its
entire scope." The debugger can always read the variable by dereferencing the
pointer. This gives perfect single-step debugging and variable inspection.

`mem2reg` promotes allocas to SSA registers and converts `dbg.declare` to
`dbg.value`. After that, the variable location becomes a register that may be
reused, merged, or eliminated — causing `<optimized out>` in the debugger and
erratic stepping behavior.

The `false &&` guard at `llvm_backend_opt.cpp:61` is evidence of a previous
attempt to conditionally skip mem2reg in debug that was abandoned.

### 1.3 The `always_preserve` flag

At `llvm_backend_debug.cpp:1166`:
```cpp
LLVMBool always_preserve = build_context.optimization_level == 0;
```

This is passed to `LLVMDIBuilderCreateAutoVariable`. At O0 it requests LLVM
preserve the variable even through optimizations, but it only helps if LLVM
can still find a location for it — which it cannot once the alloca is gone.

### 1.4 Debug locations are set selectively, not universally

`llvm_backend_stmt.cpp` calls `LLVMSetCurrentDebugLocation2` at specific
statement boundaries (lines 812, 851, 987, 1032, 1119, etc.) but not on every
emitted instruction. Instructions between location-setting points inherit the
last set location, which can cause the debugger to appear to "stay on" one
line through multiple operations or jump unexpectedly.

### 1.5 Inline memcpy/memset threshold is 8 bytes

`llvm_backend.hpp:628-630`:
```cpp
gb_internal gb_inline i64 lb_max_zero_init_size(void) {
    return cast(i64)(8);
}
```

Any struct copy or zero-init >8 bytes generates a `llvm.memmove`/`llvm.memcpy`
**call** rather than `llvm.memcpy.inline`. In debug mode (no memcpyopt pass),
these remain as actual function calls in the final binary. Structs of 16, 32,
even 64 bytes go through libc memcpy.

### 1.6 Startup/cleanup procedures always `optnone`

`llvm_backend.cpp:2138-2139, 2158-2159`:
```cpp
lb_add_attribute_to_proc(p->module, p->value, "optnone");
lb_add_attribute_to_proc(p->module, p->value, "noinline");
```

These are unconditional regardless of optimization level.

---

## 2. Safe Debug-Mode Improvements (preserve `dbg.declare` model)

These changes improve debug build performance **without** breaking the
alloca-based debug info model. No variable will become `<optimized out>`.

### 2.1 Add a minimal debug pass pipeline

In `llvm_backend_passes.cpp`, change the `-1` and `0` cases to run a small
set of passes that do not destroy allocas:

```
case -1:
    "function(memcpyopt,simplifycfg<...>),always-inline,function(annotation-remarks)"
case 0:
    "function(early-cse<>,memcpyopt,dse,simplifycfg<...>),always-inline,function(annotation-remarks)"
```

The `-1` (debug) case omits `early-cse` and `dse` to preserve intermediate
values visible during single-stepping. The `0` case includes them since it
prioritizes performance over step-through fidelity.

**Safe passes** (do not eliminate allocas or convert `dbg.declare`):
- `memcpyopt` — converts sequences like load+store into memcpy, and optimizes
  memcpy chains. Does not remove allocas.
- `simplifycfg` — merges trivially redundant basic blocks. Does not affect
  variable storage.

**Marginal passes** (alloca-safe but degrade debug stepping):
- `early-cse<>` — eliminates redundant loads from the same alloca within a
  basic block. The alloca still exists and the debugger can read it, but
  stepping through code that reads a variable multiple times may show stale
  values because the redundant load was removed. Consider for `-opt:0` but
  not for `-debug` (`-1`).
- `dse` (dead store elimination) — removes stores that are immediately
  overwritten. The alloca persists, but intermediate values that a user
  expects to see while stepping are lost. Same gating recommendation as
  `early-cse`.

**Unsafe passes** (must NOT be added at debug):
- `mem2reg` — destroys allocas, converts `dbg.declare` to `dbg.value`
- `sroa` — splits allocas into pieces, same problem as mem2reg
- `instcombine` — can fold away loads in ways that lose debug locations
- `gvn` — can eliminate loads across blocks, removing alloca reads

### 2.2 Raise inline memcpy threshold

Change `lb_max_zero_init_size()` in `llvm_backend.hpp:629` from 8 to 32:
```cpp
return cast(i64)(32);
```

This causes `llvm.memcpy.inline` / `llvm.memmove.inline` to be used for
structs up to 32 bytes (4 `mov` instructions on x86-64). LLVM's code
generator will expand these inline even at O0, avoiding function call
overhead for common small-struct operations. 64 bytes was considered but
risks code-size bloat on cold paths — 32 covers the majority of small
structs (2-4 fields) while keeping icache pressure reasonable. This
threshold applies at all optimization levels.

### 2.3 Respect optimization level for startup/cleanup

In `llvm_backend.cpp:2138-2139, 2158-2159`, guard with:
```cpp
if (build_context.optimization_level <= 0) {
    lb_add_attribute_to_proc(p->module, p->value, "optnone");
    lb_add_attribute_to_proc(p->module, p->value, "noinline");
}
```

---

## 3. LLVM Metadata and Attributes (all optimization levels)

### 3.1 Use `inbounds` GEPs (carefully)

`llvm_backend_general.cpp:372` uses `LLVMBuildGEP2`. Two call sites already
use `LLVMBuildInBoundsGEP2` (`llvm_backend_proc.cpp:3854`,
`llvm_backend_const.cpp:921`).

**`inbounds` introduces undefined behavior in LLVM IR.** If the GEP result
is ever out of bounds, `inbounds` produces a poison value. Odin avoids UB
as a guiding principle, so `inbounds` must only be added where the compiler
can **statically guarantee** the access is in-bounds — not where it is
"probably" in-bounds.

**Safe to mark `inbounds`:**
- Struct field access in `lb_emit_epi` — field offsets are compile-time
  constants within a known struct layout. This is the primary target.

**NOT safe to mark `inbounds`:**
- Array indexing, even after bounds checks — the check may be elided or
  the index may come from `#no_bounds_check`. The compiler does not
  currently track whether a bounds check has been proven.
- Multi-pointer arithmetic from user code.
- Raw pointer operations, union field access, one-past-end pointers.
- `lb_emit_ptr_offset` and general pointer arithmetic — these operate on
  user-facing pointer types where out-of-bounds is possible.

Limit the initial change to `lb_emit_epi` (`llvm_backend_general.cpp:357-375`)
for struct field GEPs only.

### 3.2 Add `dereferenceable` to indirect parameters

`llvm_backend_proc.cpp:272-308` — parameters passed by indirect reference
(`lbArg_Indirect`) get `readonly` but never `dereferenceable(N)`.

For every parameter where `ft->args[i].kind == lbArg_Indirect`, add:
```cpp
lb_add_proc_attribute_at_index_with_int(p, offset+parameter_index,
    "dereferenceable", type_size_of(e->type));
```

This tells LLVM the pointer is valid for N bytes, enabling speculative loads
and hoisting.

### ~~3.3 Add explicit alignment to loads and stores~~ — ALREADY DONE

`LLVMSetAlignment` is already called on loads and stores throughout the
codebase (18+ call sites across `llvm_backend_general.cpp` and
`llvm_backend_proc.cpp`). No action needed.

### 3.4 Emit `@llvm.assume` after nil checks (O1+ only)

Odin allows nil pointers, so `nonnull` cannot be applied to parameters in
general. However, after user code has **explicitly checked** for nil, the
compiler can inform LLVM that the pointer is non-null within that branch.

When lowering an if-statement like `if ptr != nil { ... }`, emit an
`@llvm.assume` intrinsic at the top of the true branch:

```llvm
%not_null = icmp ne ptr %p, null
call void @llvm.assume(i1 %not_null)
```

`@llvm.assume` is a zero-cost hint — it generates no machine code. LLVM's
optimizer uses it for alias analysis, load speculation, devirtualization,
and eliminating redundant nil checks downstream.

**Implementation complexity:** This requires pattern-matching nil comparisons
in `lb_build_if_stmt`. The simple `if ptr != nil { ... }` case is
straightforward, but correct handling requires covering:
- `if ptr == nil { return }` (assume in fall-through after early return)
- Chained conditions (`if ptr != nil && ptr.field != nil`)
- `or_else` patterns

Start with the simple `!= nil` / `== nil` + early-return cases only.
More complex patterns can be added incrementally.

**Gate behind `optimization_level > 0`** — at O0/debug the assume would be
dead weight since no optimization passes consume it.

The `lower-expect` and optimization passes in the O1+ pipeline already
propagate assume information through the IR.

### 3.5 Add `invariant.load` for constant globals

Loads from read-only global data (e.g., string literals, constant tables)
should get `!invariant.load` metadata. This allows LLVM to hoist them out
of loops and CSE them across basic blocks.

In `lb_emit_load`, when the source is a global constant:
```cpp
if (LLVMIsGlobalConstant(value.value)) {
    unsigned kind = LLVMGetMDKindIDInContext(ctx, "invariant.load", 14);
    LLVMSetMetadata(v, kind, LLVMMDNodeInContext2(ctx, nullptr, 0));
}
```

**Note:** Verify that `LLVMIsGlobalConstant` covers all intended cases
(string literals, constant lookup tables, enum backing arrays). Odin's
string literals may be represented as structs containing a pointer to
constant data rather than direct global constants — test before relying
on this check alone.

### 3.6 Branch weights for `#likely` / `#unlikely`

Odin has `#likely` and `#unlikely` attributes on if-statements. These are
currently not propagated to LLVM IR. The new pass pipeline already includes
`lower-expect` — but no `@llvm.expect` intrinsics are emitted.

In `lb_emit_if` (`llvm_backend_general.cpp:2833-2856`), when the branch
has a likely/unlikely annotation, emit `@llvm.expect.i1` on the condition
before the `LLVMBuildCondBr`. This gives LLVM block placement and
if-conversion information.

### 3.7 `mustprogress` in debug builds

`llvm_backend_proc.cpp:190-192`:
```cpp
if (!pt->Proc.diverging && build_context.optimization_level > 0) {
    lb_add_attribute_to_proc(m, p->value, "mustprogress");
}
```

`mustprogress` is valid in all build modes (it's a semantic property of the
procedure, not an optimization hint). Remove the `optimization_level > 0`
guard.

---

## 4. Larger Structural Improvements

### 4.1 Assignment tracking (`llvm.dbg.assign`) — enables mem2reg in debug

LLVM 16+ introduced **assignment tracking** as a replacement for
`dbg.declare`/`dbg.value`. It was designed specifically to survive mem2reg
and SROA while maintaining accurate debug info.

The compiler would need to:
1. Call `LLVMDIBuilderInsertDbgAssign` instead of `InsertDeclare`
2. Attach assignment markers to every store to a debug variable
3. Enable `declare-to-assign` in the pass pipeline

This unlocks mem2reg in debug builds without losing variable inspection.
Variables get tracked through SSA transformations with correct locations.

**API status:** As of LLVM 20, `LLVMDIBuilderInsertDbgAssign` is **not** in
the C API. However, LLVM 19+ moved to the "debug records" model (away from
intrinsics), and the C API does expose `LLVMDIBuilderInsertDeclareRecordAtEnd`
and `LLVMDIBuilderInsertDbgValueRecordAtEnd` (the codebase already uses the
declare variant via a compat macro at `llvm_backend.hpp:46-48`). Assignment
tracking would require either a C++ wrapper or an upstream C API patch.

**Risk:** Assignment tracking is still marked experimental in some LLVM
versions. The debug records migration (LLVM 19+) is a separate but related
architectural shift — any work here should target the records model, not the
deprecated intrinsics model. Needs testing across debuggers (GDB, LLDB,
WinDbg).

### 4.2 Complete debug location coverage

Audit all instruction emission paths to ensure `LLVMSetCurrentDebugLocation2`
is called before every instruction that could correspond to a source location.
Currently, locations are set at statement boundaries but not at expression
sub-steps, causing stepping to skip over operations.

This is independent of optimization level and improves debug experience at
all levels.

### 4.3 DW_OP expressions for complex variable locations

`llvm_backend_debug.cpp:1181` always creates an empty debug expression:
```cpp
LLVMDIBuilderCreateExpression(m->debug_builder, nullptr, 0);
```

For variables accessed through a known offset (e.g., struct fields, array
elements with constant index), emit `DW_OP_plus_uconst` expressions. This
allows debuggers to display sub-fields even when the base address is all
that's tracked.

---

## 5. Intentional Design Decisions (do NOT change)

### 5.1 No `nsw`/`nuw` flags on arithmetic

`llvm_backend_opt.cpp:20-31` documents that Odin defines integer overflow as
2's complement wrapping. Adding `nsw`/`nuw` to arithmetic would cause
miscompilation. This is correct and must not change.

### 5.1a Poison values are safe when preconditions are statically guaranteed

The comment in `llvm_backend_opt.cpp:20-31` broadly rejects "poison-value
based optimizations," but this conflates two distinct things:

1. **`nsw`/`nuw` on arithmetic** — these produce poison on overflow, letting
   LLVM assume overflow doesn't happen. Since Odin wraps, these are correctly
   forbidden.

2. **Poison as an LLVM mechanism** — many annotations produce poison values
   when their precondition is violated (`inbounds`, `exact`, `dereferenceable`,
   etc.), but poison only causes undefined behavior when it reaches a
   **side-effecting instruction** (store, branch, return, call argument).
   Poison that is never observed is harmless.

The guiding principle for Odin: **a poison-producing annotation is safe if
the compiler can statically guarantee the precondition always holds.** The
precondition must not depend on runtime values or user code behavior.

**Safe uses (precondition is structural, not runtime):**
- `inbounds` on struct field GEPs — field offsets are compile-time constants
  within a known layout. Cannot be violated at runtime.
- `dereferenceable(N)` on ABI-indirect parameters — the calling convention
  guarantees the caller constructed a valid object of known size.
- `invariant.load` on loads from `LLVMIsGlobalConstant` globals — the
  global is immutable by construction.

**Unsafe uses (precondition depends on runtime):**
- `nsw`/`nuw` on user arithmetic — overflow depends on runtime values.
- `inbounds` on array indexing — the index comes from user code and may be
  out of bounds (especially under `#no_bounds_check`).
- `nonnull` on user-facing pointer parameters — Odin allows nil pointers.
- `exact` on user division/shift — depends on runtime operand values.

This distinction allows the improvements in sections 3.1, 3.2, and 3.5
without violating Odin's no-UB principle. Each recommendation in this
document is designed so that the annotation's precondition is provably
true by construction, never conditionally true based on runtime state.

### 5.2 TBAA implementation

TBAA root, omnipotent char, and per-type access tags are correctly generated
(`llvm_backend_general.cpp:1104-1113`) and applied to loads and stores.

### 5.3 Function attributes

`nounwind`, `willreturn`, `noalias`, `nocapture`, `readonly` are properly
emitted where applicable (`llvm_backend_proc.cpp:172-308`,
`llvm_backend.cpp:258-271`).

### 5.4 Nil pointers are valid

Odin allows nil pointers by design. `nonnull` cannot be applied to pointer
parameters in general. The existing `nonnull` on the equal procedure's
parameters (`llvm_backend.cpp:268-269`) is correct because it is a
compiler-generated function with known non-null inputs. Non-null information
is instead communicated via `@llvm.assume` after explicit user nil checks
(see 3.4).

---

## 6. Priority Order

| # | Change | Impact | Risk | Preserves debug info |
|---|--------|--------|------|---------------------|
| 1 | Raise memcpy inline threshold to 32 | High | None | Yes |
| 2 | Add safe passes to debug pipeline (`-1`: memcpyopt+simplifycfg; `-opt:0`: +early-cse+dse) | High | Low | Yes |
| 3 | Use `inbounds` GEPs for struct field access only | Medium | Low (UB if misapplied) | Yes |
| 4 | Add `dereferenceable` to indirect params | Medium | None | Yes |
| ~~5~~ | ~~Add explicit alignment to loads/stores~~ | — | — | Already done |
| 6 | Emit `@llvm.assume` after nil checks (O1+, simple patterns first) | Medium | Low | N/A (O1+ only) |
| 7 | Respect opt level for startup/cleanup | Low | None | Yes |
| 8 | Add `mustprogress` in all build modes | Low | None | Yes |
| 9 | Emit `@llvm.expect` for `#likely`/`#unlikely` | Low | None | Yes |
| 10 | Add `invariant.load` for const globals (verify coverage first) | Low | Low | Yes |
| 11 | Assignment tracking (target debug records model, needs C API work) | Very High | High | Designed to |
| 12 | Complete debug location coverage | Medium | Low | Yes |
| 13 | DW_OP expressions for complex locations | Low | Medium | Yes |

Items 1-4, 6-10 are safe, incremental changes. Item 5 is already implemented.
Items 11-13 are larger structural work. Item 11 is the eventual path to having
both fast debug builds and accurate debug info, but requires C API extension
work and should target LLVM's debug records model (not the deprecated
intrinsics model).
