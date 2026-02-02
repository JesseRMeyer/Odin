# IR Codegen Improvement Plan

Improvements to the LLVM IR the Odin compiler emits, independent of
which optimization passes run. These reduce work for the backend at
all optimization levels and particularly benefit debug builds where
few or no LLVM passes run.

**Key files:**
- `src/llvm_backend_general.cpp` — `lb_emit_if`, `lb_emit_load`, `lb_build_cond`
- `src/llvm_backend_expr.cpp` — `lb_emit_conv`, `lb_emit_comp`, `lb_build_addr_compound_lit`
- `src/llvm_backend_stmt.cpp` — `lb_build_range_interval`, `lb_build_if_stmt`
- `src/llvm_backend_utility.cpp` — `lb_mem_zero_ptr`, `lb_add_local`

---

## 1. Eliminate bool i1→i8→i1 round-trip

### Problem

Every comparison-then-branch goes through three steps:

```llvm
%1 = icmp ne ptr %0, null        ; i1
%2 = zext i1 %1 to i8            ; i8  (Odin's bool)
%3 = icmp ne i8 %2, 0            ; i1  (for branch)
br i1 %3, ...
```

The `zext` and second `icmp` are always a no-op. This affects every
`if`, `for` condition, `&&`, `||`, and ternary in the entire program.
At O1+ LLVM removes them instantly, but at `-debug` they survive as
real instructions.

### Root cause

1. `lb_emit_comp` (llvm_backend_expr.cpp:3341) produces `res.type = t_llvm_bool` (i1).
2. The caller does `lb_emit_conv(p, cmp, type)` where `type` is `t_bool` (i8).
   This hits llvm_backend_expr.cpp:2045: `LLVMBuildZExt(i1 → i8)`.
3. `lb_build_cond` (llvm_backend_general.cpp:3625) does
   `lb_emit_conv(p, v, t_llvm_bool)` to convert back.
   This hits llvm_backend_expr.cpp:2039: `LLVMBuildICmp(LLVMIntNE, i8, 0)`.
4. `lb_emit_if` (llvm_backend_general.cpp:2857) does another
   `LLVMBuildTruncOrBitCast` to i1, which is redundant after step 3.

### Fix

Modify `lb_build_cond` to skip the i8 materialization when the value
will only be used as a branch condition. Two changes:

**A.** In `lb_build_cond` (llvm_backend_general.cpp:3619-3631), when
the expression is built and its type is already `t_llvm_bool` (i1),
skip the `lb_emit_conv(p, v, t_llvm_bool)`:

```cpp
v = lb_build_expr(p, cond);
if (v.type != t_llvm_bool) {
    v = lb_emit_conv(p, v, t_llvm_bool);
}
```

This handles the case where `lb_build_expr` returns a comparison result
that hasn't been widened to i8 yet. But the actual widening happens
inside `lb_build_expr` → `lb_build_binary_expr` which calls
`lb_emit_conv(cmp, type)` where `type = default_type(tv.type) = t_bool`.

**B.** The deeper fix: in `lb_build_binary_expr` for comparison
operators (llvm_backend_expr.cpp:1879-1892), when the result will only
be used as a branch condition, avoid the `lb_emit_conv` to `t_bool`.
However, the compiler doesn't know at expression-build time whether the
result is used as a branch condition or a value.

**Practical approach:** Add a fast-path in `lb_emit_conv` that
recognizes the i1→i8→i1 round-trip and short-circuits it. In the
`bool → llvm_bool` conversion (llvm_backend_expr.cpp:2039-2044),
check if the i8 value was produced by a `zext i1`:

```cpp
if (is_type_boolean(src) && dst == t_llvm_bool) {
    // Check if value is a zext from i1 — if so, use the original i1
    if (LLVMIsAZExtInst(value.value)) {
        LLVMValueRef operand = LLVMGetOperand(value.value, 0);
        if (LLVMTypeOf(operand) == LLVMInt1TypeInContext(ctx)) {
            lbValue res = {};
            res.value = operand;
            res.type = t;
            return res;
        }
    }
    // fallback: emit icmp ne i8 %x, 0
    lbValue res = {};
    res.value = LLVMBuildICmp(p->builder, LLVMIntNE, value.value,
                              LLVMConstNull(lb_type(m, src)), "");
    res.type = t;
    return res;
}
```

Also, in `lb_emit_if` (llvm_backend_general.cpp:2857-2858), check if
the value is already i1 before calling `LLVMBuildTruncOrBitCast`:

```cpp
LLVMValueRef cv = cond.value;
if (LLVMTypeOf(cv) != lb_type(p->module, t_llvm_bool)) {
    cv = LLVMBuildTruncOrBitCast(p->builder, cv, lb_type(p->module, t_llvm_bool), "");
}
LLVMBuildCondBr(p->builder, cv, true_block->block, false_block->block);
```

### Impact

Eliminates 2 instructions per branch at all optimization levels.
Every `if`, `for`, `switch`, `&&`, `||` benefits.

### Risk

Low. The `LLVMIsAZExtInst` check is conservative — it only
short-circuits when it can prove the operand is already i1. The
fallback path is the existing behavior.

---

## 2. Skip redundant zero-init for fully-initialized struct literals

### Problem

Every struct literal construction follows this pattern:

```llvm
%tmp = alloca %Vec3
call void @llvm.memset(ptr %tmp, i8 0, i64 24)   ; zero all bytes
store double %x, ptr (gep %tmp, 0, 0)             ; overwrite field 0
store double %y, ptr (gep %tmp, 0, 1)             ; overwrite field 1
store double %z, ptr (gep %tmp, 0, 2)             ; overwrite field 2
```

The memset is dead — every field is immediately written. But padding
bytes between fields must remain zero (for `==`, hashing, serialization).

### Root cause

`lb_build_addr_compound_lit` (llvm_backend_expr.cpp:5040) creates the
temp alloca with `lb_add_local_generated(p, type, true)` — the `true`
requests zero-init. Then `lb_add_local` (llvm_backend_general.cpp:3657)
forces zero-init for any struct with padding regardless.

### Fix

When **all** fields of a struct literal have explicit values (no
omitted fields), replace the memset + field-stores with a single
constant store when all values are constant, or skip the memset when
the struct has no padding.

**A.** In `lb_build_addr_compound_lit`, case `Type_Struct`
(llvm_backend_expr.cpp:5265-5272):

Before the field-store loop, check if all fields are provided:

```cpp
bool all_fields_set = (cl->elems.count == st->fields.count);
```

**B.** If `all_fields_set` and the struct has no padding, create the
alloca with `zero_init=false`:

```cpp
bool has_padding = (type_size_of_struct_pretend_is_packed(bt) != type_size_of(bt));
bool needs_zero_init = has_padding || !all_fields_set;
// Use needs_zero_init instead of unconditional true
```

**C.** If `all_fields_set` and the struct **has** padding, keep the
memset but consider replacing it with a constant aggregate store when
all field values are constant (which `lb_const_value` already handles
at line 5272 — verify it produces a fully-defined constant including
padding zeros).

Actually, the existing code at line 5272 already does:
```cpp
lb_addr_store(p, v, lb_const_value(p->module, type, exact_value_compound(expr)));
```
This stores a complete constant (with zero padding) before the field
stores. So for **constant** struct literals, the memset at alloca
creation is redundant with the constant store at line 5272. The fix is
to pass `false` for `zero_init` when the constant store will
immediately follow:

```cpp
// In lb_build_addr_compound_lit, for Type_Struct with cl->elems.count > 0:
// The lb_addr_store of lb_const_value already writes all bytes including padding.
// No need to zero-init the alloca first.
lbAddr v = lb_add_local_generated(p, type, /*zero_init=*/false, /*force_no_init=*/true);
```

The `force_no_init=true` bypasses the padding check in `lb_add_local`
(line 3657-3670) that would otherwise re-enable zero-init.

### Impact

Eliminates one memset per struct/array literal construction. High
frequency — struct literals are extremely common.

### Risk

Low-medium. Must verify that `lb_const_value` with
`exact_value_compound` produces a fully-defined LLVM constant that
includes zero padding bytes. If any field is omitted from the compound
literal, the constant still has zero for that field. The only risk is
if `lb_const_value` produces `undef` for missing fields instead of
zero — audit this.

---

## 3. Eliminate duplicate loop index alloca in for-range

### Problem

`for i in 0..<n` generates three allocas:

```llvm
%i  = alloca i64        ; range iterator (incremented each iteration)
%2  = alloca i64        ; internal counter (tracks iteration count)
%i1 = alloca i64        ; body-visible copy of i
```

Each iteration does:
```llvm
load %i → store %i1     ; copy iterator to body variable
load %i1                 ; body reads from copy
```

The `%i` → `%i1` copy is unnecessary. The loop body could read
directly from `%i`.

### Root cause

`lb_build_range_interval` (llvm_backend_stmt.cpp:784) creates `value`
(the iterator alloca). Then at the top of the loop body (line ~824),
it loads from `value` and stores to a new alloca for the loop body
variable. This is because the general range codegen supports
`for x, i in collection` where the value and index are separate
concepts — but for integer ranges, the value **is** the index.

The `%2` counter alloca exists to track the second range variable
(`val1` — the iteration count). For `for i in 0..<n`, there's no
second variable, so `val1` is blank and `index` gets a generated
local (line 795) that's never read by user code.

### Fix

**A.** When `val1` is blank (no second variable), skip creating the
`index` alloca entirely. In `lb_build_range_interval`
(llvm_backend_stmt.cpp:790-797):

```cpp
lbAddr index = {};
if (val1_type != nullptr) {
    Entity *e = entity_of_node(val1);
    index = lb_add_local(p, val1_type, e, false);
    lb_addr_store(p, index, lb_const_int(m, t_int, 0));
}
// Only increment index in the loop body if index.addr.value != nullptr
```

**B.** Eliminating the `%i` → `%i1` body copy is harder because it
affects debug info — `dbg.declare` on `%i1` tells the debugger where
`i` lives in the loop body scope. Merging them would require the
debugger to understand that `%i` is `i`. This is already the case if
the entity is the same. Check whether `val0` and the body variable
share the same entity — if so, the copy can be skipped and
`dbg.declare` attached directly to `%i`.

This optimization is lower priority than (A) since the load→store→load
chain is efficiently handled by `memcpyopt` in the debug pass pipeline.

### Impact

Eliminates 1 alloca + 2 loads + 2 stores per loop iteration for the
common single-variable range loop. Moderate frequency.

### Risk

Low for (A). The counter alloca is provably unused when `val1` is blank.
Medium for (B) — debug info correctness must be verified.

---

## 4. Write struct return directly to sret pointer

### Problem

In `add_vec`, the return value is built in a temp alloca, then
memcpy'd to the sret pointer:

```llvm
%tmp = alloca %Vec3
call void @llvm.memset(ptr %tmp, i8 0, i64 24)    ; zero temp
; ... store fields to %tmp ...
call void @llvm.memcpy.inline(ptr %agg.result, ptr %tmp, i64 24)
ret void
```

The temp alloca and memcpy are unnecessary — the fields could be stored
directly to `%agg.result`.

### Root cause

`lb_build_addr_compound_lit` always creates a local temp for the struct
literal. The caller then copies the result to wherever it's needed. For
return statements, `lb_build_return_stmt_internal`
(llvm_backend_stmt.cpp:2334-2343) copies the value to the sret pointer.
But the compound literal doesn't know it's being returned — it builds
into a temp unconditionally.

### Fix

This is a special case of a more general "destination-driven codegen"
pattern. The full fix (passing the destination address down into
expression codegen) is a large refactor. A targeted fix for the return
case:

**A.** In `lb_build_return_stmt_internal`, when `return_by_pointer` is
true and the return expression is a compound literal, pass the sret
pointer directly as the target for `lb_build_addr_compound_lit`:

This requires adding an optional `target_addr` parameter to
`lb_build_addr_compound_lit`. When provided, it uses the target instead
of creating a local:

```cpp
gb_internal lbAddr lb_build_addr_compound_lit(lbProcedure *p, Ast *expr,
                                              lbAddr *target = nullptr) {
    // ...
    lbAddr v;
    if (target != nullptr) {
        v = *target;
    } else {
        v = lb_add_local_generated(p, type, true);
    }
```

Then in the return statement handler, detect compound lit returns and
pass the sret pointer.

**B.** Simpler alternative: rely on the `memcpyopt` pass (now enabled
in debug builds) to merge the stores + memcpy. This already happens —
`memcpyopt` is specifically designed to forward stores through memcpy.
Verify with IR output that this optimization fires in debug mode.

### Impact

Eliminates 1 alloca + 1 memset + 1 memcpy per struct-returning
function call. Medium frequency.

### Risk

Medium for (A) — must ensure the target address is valid for the
lifetime of the compound literal construction, and that no aliasing
occurs. The sret pointer is `noalias`, so this is safe.
Low for (B) — relies on existing pass.

---

## 5. Bounds checks: inline the comparison (optional)

### Problem

Array bounds checks emit an unconditional call to
`runtime::bounds_check_error`, which internally does:

```odin
bounds_check_error :: proc(file, line, column, index, count) {
    if uint(index) < uint(count) { return }
    handle_error(...)  // noreturn
}
```

The happy path (in-bounds) requires a function call, argument setup (5
args including string+line+col), and a return. At O1+, LLVM inlines
this and the overhead vanishes. At debug, it's 5 argument stores + a
call + a compare + a return per array access.

### Current design rationale

The call-based design keeps the IR simple and the bounds-check function
small. At O1+, LLVM inlines it and the result is identical to an inline
check. The design is intentional and well-reasoned.

### Possible optimization

Emit the comparison inline and only call the error handler on failure:

```llvm
%ok = icmp ult i64 %index, %count
br i1 %ok, label %in_bounds, label %out_of_bounds

out_of_bounds:
  call void @runtime::bounds_check_error(...)
  unreachable

in_bounds:
  ; continue
```

This avoids the call overhead on the hot path at all optimization
levels. The cold path (out of bounds) still calls the error handler.

### Impact

Eliminates function call overhead per array access in debug builds.
The `unreachable` after the error call also gives LLVM information that
the out-of-bounds path doesn't continue, which helps even at O0.

### Risk

Medium. Increases IR size (1 branch + 2 blocks per bounds check vs 1
call). May slightly increase compile time. The existing design was
chosen deliberately — changing it should be tested for both compile
time and debug code size impact.

**Recommendation:** Benchmark this separately. If debug-mode array-heavy
code is a bottleneck, it's worth doing. Otherwise, the current design
is fine.

---

## Priority Order

| # | Change | Impact per site | Frequency | Risk |
|---|--------|-----------------|-----------|------|
| 1 | i1→i8→i1 short-circuit | 2 instructions | Every branch | Low |
| 2 | Skip zero-init for struct literals | 1 memset | Every struct literal | Low-Medium |
| 3 | Skip unused range counter alloca | 1 alloca + 4 mem ops/iter | Every `for i in` | Low |
| 4 | Direct sret struct return | 1 alloca + memset + memcpy | Every struct return | Medium |
| 5 | Inline bounds comparison | 1 call + 5 args | Every array access | Medium |

Items 1-3 are safe, mechanical changes. Item 4 has a simple fallback
(rely on `memcpyopt`). Item 5 is a design tradeoff that should be
benchmarked independently.
