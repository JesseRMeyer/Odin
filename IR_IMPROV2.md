# IR Generation Improvements — Phase 2

## Context

Phase 1 (already merged to master via `ir-codegen-improvements`) introduced SSA aggregate
primitives (`lb_emit_struct_iv`, `lb_build_struct_value`, `lb_make_slice_value`,
`lb_make_string_value`), applied them to multi-return tuples, slice/string value
construction, and ABI struct coercion, added emission-time peepholes, and introduced
`select` for scalar ternary expressions with trivial arms.

This document proposes the next set of improvements: converting remaining alloca-based
aggregate construction to SSA, adding `nounwind` to Odin-CC functions, extending `select`
emission to more expression forms, and completing the slice SSA value path for Array and
MultiPointer source types.

Every change preserves Odin semantics exactly. The IR changes are invisible to programs.

---

## 1. `nounwind` on Odin Calling Convention Functions

### What

Mark all `ProcCC_Odin` and `ProcCC_Contextless` function definitions as `nounwind`.

### Why

Without `nounwind`, LLVM must conservatively assume every call can unwind. This blocks:
- Dead store elimination before calls
- Tail call optimization
- Removal of unwind tables
- `willreturn` inference (which gates dead call elimination for pure functions)

### Safety Argument

Odin has no exception mechanism. The backend never emits `invoke`, `landingpad`, `resume`,
or personality functions — only `call`. All panics terminate via `llvm.trap` (hardware
trap / process abort), which does not unwind the stack. The `setjmp`/`longjmp` usage in
the codebase is compiler-internal (JIT evaluator in `llvm_backend_comp.cpp`), never
in emitted code.

`nounwind` is safe for any function whose body is entirely Odin code, because Odin code
cannot throw. Odin-CC functions (`ProcCC_Odin`, `ProcCC_Contextless`) satisfy this:
they are always implemented in Odin (they carry the implicit context parameter or its
absence), so no foreign code can be declared with these calling conventions.

### Why NOT foreign functions

Foreign function declarations (`ProcCC_CDecl`, `ProcCC_StdCall`, `ProcCC_Win64`,
`ProcCC_SysV`, etc.) must NOT receive `nounwind` unconditionally. A user can
`foreign import` a C++ library whose functions throw exceptions. Adding `nounwind` to
such a declaration is immediate undefined behavior — LLVM will assume the function does
not unwind and may corrupt the stack.

Note: the existing `-disable-unwind` flag at `llvm_backend_proc.cpp:156` already applies
`nounwind` to foreign procs. This is arguably a latent bug (contrast with `noredzone` at
line 168 which correctly checks `!entity->Procedure.is_foreign`), but fixing it is outside
scope here. The new unconditional `nounwind` for Odin-CC is orthogonal.

### Where

`src/llvm_backend_proc.cpp`, `lb_create_procedure`, after line 158:

```cpp
// Existing conditional nounwind for all procs (user opt-in via -disable-unwind)
if (build_context.disable_unwind) {
    lb_add_attribute_to_proc(m, p->value, "nounwind");
}

// NEW: Odin-CC functions cannot unwind — Odin has no exception mechanism.
// All panics terminate via llvm.trap. Only applies to Odin-implemented
// functions (ProcCC_Odin, ProcCC_Contextless), never to foreign declarations.
if (!build_context.disable_unwind) {  // avoid duplicate attribute
    ProcCallingConvention cc = pt->Proc.calling_convention;
    if (cc == ProcCC_Odin || cc == ProcCC_Contextless) {
        lb_add_attribute_to_proc(m, p->value, "nounwind");
    }
}
```

The guard `!build_context.disable_unwind` avoids adding the attribute twice when the
user already passed `-disable-unwind` (which applies it to everything).

### Risk

None. This is a pure attribute addition that tells LLVM something already true.

---

## 2. SSA Aggregate Construction for Complex and Quaternion Arithmetic

### What

Replace alloca+GEP+store+load with `lb_build_struct_value` in complex and quaternion
add/sub operations.

### Current Code (`llvm_backend_expr.cpp:1488-1529`, complex)

```
alloca res
compute real, imag
GEP res.0 → store real
GEP res.1 → store imag
load res
```

### Proposed Code

```
compute real, imag
return lb_build_struct_value(p, type, {real, imag}, 2)
```

This produces `insertvalue (insertvalue poison, real, 0), imag, 1` — a pure SSA value
with no memory traffic.

### Same pattern for quaternion add/sub (`llvm_backend_expr.cpp:1542-1587`)

Replace the 4-field alloca+GEP+store+load with:
```
return lb_build_struct_value(p, type, {z0, z1, z2, z3}, 4)
```

### Quaternion multiply

Not addressed here. Quaternion multiply (`llvm_backend_expr.cpp:1588+`) dispatches to
a runtime procedure call (`__$quaternionMul*`), so the result construction is handled
by the call return path, not by inline aggregate construction.

### Safety

The values computed (`real`, `imag`, `z0`–`z3`) are identical. Only the assembly method
changes from memory to SSA. `lb_build_struct_value` uses `lb_emit_struct_iv` which calls
`lb_convert_struct_index` for proper field remapping — the same index mapping used by
`lb_emit_struct_ep` in the current code.

### Risk

Low. The only subtlety is the `@QuaternionLayout` field ordering. The current code stores
to fields 0, 1, 2, 3 in that order, which is the LLVM struct layout order (not the
semantic i/j/k/w order). `lb_build_struct_value` takes fields in LLVM struct order, so
the mapping is identity. Verify by inspecting `lb_convert_struct_index` for quaternion
types — it should pass through indices unchanged for the LLVM-level struct.

---

## 3. SSA Aggregate Construction for `any` Type

### What

Replace alloca+GEP+store+load with `lb_build_struct_value` in `any` construction.

### Current Code (`llvm_backend_expr.cpp:2848-2864`)

```
alloca result (zero-init)
data = lb_address_from_load_or_generate_local(value)
data = conv(data, rawptr)
id = lb_typeid(st)
GEP result.0 → store data
GEP result.1 → store id
load result
```

### Proposed Code

```
data = lb_address_from_load_or_generate_local(value)
data = conv(data, rawptr)
id = lb_typeid(st)
return lb_build_struct_value(p, t, {data, id}, 2)
```

The `any` type is a 2-field struct `{rawptr, typeid}`. Both fields are always assigned,
so the zero-init of the alloca was redundant even before this change.

Note: `lb_address_from_load_or_generate_local` is still called because `any` requires a
*pointer* to the data. That function's alloca is unavoidable when the source value is an
SSA register — the data must exist in memory for the `any` to point at it. What we
eliminate here is the *second* alloca for the `any` struct itself.

### Safety

Identical semantics. The `any` struct fields are `{data: rawptr, id: typeid}` at Odin
field indices 0 and 1. `lb_convert_struct_index` maps these to LLVM struct indices 0
and 1 (no padding fields). The values stored are the same.

### Risk

None. This is a mechanical replacement of 2-field struct construction.

---

## 4. SSA Aggregate Construction for Complex/Quaternion Conversions

### What

Replace all 7 conversion cases in `llvm_backend_expr.cpp:2234-2307` with `insertvalue`
chains.

### Cases

| Conversion | Fields | Current | Proposed |
|---|---|---|---|
| complex→complex | 2 | alloca, store 2 | `lb_build_struct_value(p, t, {real, imag}, 2)` |
| quaternion→quaternion | 4 | alloca, store 4 | `lb_build_struct_value(p, t, {q0, q1, q2, q3}, 4)` |
| int→complex | 1+zero | alloca(zero), store 1 | `insertvalue(zero, real, 0)` |
| float→complex | 1+zero | alloca(zero), store 1 | `insertvalue(zero, real, 0)` |
| int→quaternion | 1+zero | alloca(zero), store 1 | `insertvalue(zero, real, 3)` |
| float→quaternion | 1+zero | alloca(zero), store 1 | `insertvalue(zero, real, 3)` |
| complex→quaternion | 2+zero | alloca(zero), store 2 | `insertvalue(insertvalue(zero, ...), ...)` |

For the partial-initialization cases (int/float→complex, int/float→quaternion,
complex→quaternion), the base aggregate is `LLVMConstNull(lb_type(m, t))` (the zero
constant) instead of `LLVMGetPoison`. Only the non-zero fields are inserted.

### @QuaternionLayout Note

The quaternion memory layout stores the real (w) component at index 3, with i/j/k at
indices 0/1/2. The current code stores to index 3 for `int→quaternion` and
`float→quaternion`. The `insertvalue` replacement must use the same index:
```cpp
lbValue zero = {LLVMConstNull(lb_type(m, t)), t};
return lb_emit_struct_iv(p, zero, real, 3);  // field 3 = w (real part)
```

For `complex→quaternion`, the current stores are to indices 3 (real) and 0 (imag):
```cpp
lbValue zero = {LLVMConstNull(lb_type(m, t)), t};
lbValue tmp = lb_emit_struct_iv(p, zero, real, 3);
return lb_emit_struct_iv(p, tmp, imag, 0);
```

### Safety

Each case is a direct transliteration from GEP+store to insertvalue using the same field
indices. The zero base replaces the zero-init alloca. The `lb_emit_struct_iv` calls go
through `lb_convert_struct_index` just like `lb_emit_struct_ep` does, so field mapping
is identical.

### Risk

Low. Must audit that `lb_convert_struct_index` for quaternion types maps index 3→3
(identity). If quaternion types have padding fields in their LLVM representation, the
index mapping would differ. Verify empirically by printing `lb_convert_struct_index(m,
quaternion_type, 3)` in a debug build.

---

## 5. SSA Aggregate Construction for Conjugate

### What

Replace alloca+GEP+store+load with `lb_build_struct_value` in `lb_emit_conjugate`
for complex and quaternion types (`llvm_backend_proc.cpp:1052-1075`).

### Current Code (complex, lines 1055-1061)

```
alloca res
extract real (field 0), imag (field 1)
imag = -imag
GEP res.0 → store real
GEP res.1 → store imag
load res
```

### Proposed Code (complex)

```
extract real (field 0), imag (field 1)
imag = -imag
return lb_build_struct_value(p, type, {real, imag}, 2)
```

### For quaternion (lines 1062-1075)

```
extract real (3), imag (0), jmag (1), kmag (2)
imag = -imag; jmag = -jmag; kmag = -kmag
return lb_build_struct_value(p, type, {imag, jmag, kmag, real}, 4)
```

Note the field order: the current code stores to fields {3, 0, 1, 2} (real, imag, jmag,
kmag). `lb_build_struct_value` takes fields in LLVM struct index order (0, 1, 2, 3),
so the array must be `{imag, jmag, kmag, real}` — matching the `@QuaternionLayout`
where index 0=i, 1=j, 2=k, 3=w.

### Array and Matrix Conjugate

Not addressed. These iterate over elements with a loop (`llvm_backend_proc.cpp:1076-1098`).
The loop writes to each element address via GEP+store, which is appropriate for
variable-count aggregates. Converting these to SSA would require building the aggregate
one element at a time via repeated `insertvalue`, which is equivalent in cost and may
actually be worse for large arrays (LLVM optimizes address-based loops better than long
insertvalue chains).

### Risk

Low. Same field indices, same values, different assembly method. The quaternion field
ordering must be double-checked: `lb_build_struct_value(p, type, fields, 4)` inserts
`fields[0]` at Odin index 0, `fields[1]` at Odin index 1, etc. The Odin indices pass
through `lb_convert_struct_index` to get LLVM indices. If quaternion Odin indices
map identity to LLVM indices (which they should, as quaternions have no padding), then
`{imag, jmag, kmag, real}` at Odin indices {0,1,2,3} is correct.

---

## 6. Extend `select` to Ternary Expressions with Side-Effect-Free Arms

### What

Broaden the `is_trivial` check in ternary select optimization to accept additional
side-effect-free expressions beyond constants and bare identifiers.

### Current Gate (`llvm_backend_expr.cpp:4123-4129`)

```cpp
auto is_trivial = [](Ast *e) -> bool {
    e = unparen_expr(e);
    TypeAndValue tav = type_and_value_of_expr(e);
    if (tav.mode == Addressing_Constant) return true;
    if (e->kind == Ast_Ident) return true;
    return false;
};
```

### Proposed Extension

Add two more cases that are provably side-effect-free:

```cpp
auto is_trivial = [](Ast *e) -> bool {
    e = unparen_expr(e);
    TypeAndValue tav = type_and_value_of_expr(e);
    if (tav.mode == Addressing_Constant) return true;
    if (e->kind == Ast_Ident) return true;
    if (e->kind == Ast_SelectorExpr) {
        // Field access: x.y — pure if x is an ident (not a method call)
        Ast *operand = e->SelectorExpr.expr;
        if (operand && unparen_expr(operand)->kind == Ast_Ident) return true;
    }
    if (e->kind == Ast_UnaryExpr) {
        // Unary expressions like -x, ~x — pure if operand is trivial
        // Exclude & (address-of) since it's not a value operation in this context
        Ast *ue = e;
        if (ue->UnaryExpr.op.kind != Token_And) {
            Ast *operand = ue->UnaryExpr.expr;
            operand = unparen_expr(operand);
            TypeAndValue otav = type_and_value_of_expr(operand);
            if (otav.mode == Addressing_Constant) return true;
            if (operand->kind == Ast_Ident) return true;
        }
    }
    return false;
};
```

### Why These Specific Cases

**Field access (`x.y` where `x` is an ident):** This covers the extremely common pattern
`cond ? a.x : b.y`. The field access is a pure operation — it extracts a value from a
struct in a register. The guard `operand->kind == Ast_Ident` ensures we don't accept
chained accesses like `f().x` where `f()` has side effects.

**Unary expressions (`-x`, `~x` where operand is trivial):** Covers patterns like
`cond ? x : -x`. Negation and bitwise complement are pure. Address-of (`&x`) is
excluded because it produces a pointer, not a scalar value, and the ternary select
path requires scalar types (already enforced by the `is_scalar` check above).

### Why NOT function calls, index expressions, etc.

- **Function calls**: Have side effects. Cannot be unconditionally evaluated.
- **Index expressions (`a[i]`)**: May trap on bounds check. Cannot be unconditionally
  evaluated without changing semantics (the non-taken branch's bounds check must not
  execute).
- **Cast expressions**: Could be added (most are pure), but the benefit is marginal
  since `lb_emit_conv` in the branch+phi path already handles them efficiently. Defer
  to a future pass.

### Safety

`select` evaluates both arms unconditionally. For the added cases:
- **Field access on an ident**: The struct value is already in a register (it was loaded
  when the ident was evaluated). `extractvalue` on a register cannot trap.
- **Unary arith on a trivial operand**: Negation and complement on integers/floats
  cannot trap. Float negation is a bit flip. Integer negation of `INT_MIN` is defined
  in LLVM as wrapping (and in Odin, which uses two's complement with wrapping semantics
  for signed overflow in release mode).

### Risk

Low-medium. The conservative approach (only idents and constants) was safe. Each
extension must be proven side-effect-free. The two cases above are. If any doubt
exists about a future extension, do not add it — the branch+phi path is always correct.

---

## 7. `or_else` Select Optimization

### What

Add a `select` fast path for `or_else` when the else expression is trivial and the
result type is scalar.

### Current Code (`llvm_backend_utility.cpp:487-519`)

The non-diverging path always creates 3 blocks + phi:
```
block or_else.then: conv(lhs, type) → jump done
block or_else.else: conv(build_expr(else_expr), type) → jump done
block or_else.done: phi [then → lhs, else → else_val]
```

### Proposed Addition

Before the non-diverging block path, add:

```cpp
} else {
    Type *bt = base_type(type);
    bool is_scalar = is_type_integer(bt) || is_type_float(bt) || is_type_boolean(bt) ||
                     is_type_pointer(bt) || is_type_enum(bt) || is_type_rune(bt) ||
                     is_type_typeid(bt);
    if (is_scalar) {
        Ast *else_unparen = unparen_expr(else_expr);
        TypeAndValue else_tav = type_and_value_of_expr(else_unparen);
        bool else_trivial = (else_tav.mode == Addressing_Constant) ||
                            (else_unparen->kind == Ast_Ident);
        if (else_trivial) {
            lbValue has_value = lb_emit_try_has_value(p, rhs);
            lbValue then_val = lb_emit_conv(p, lhs, type);
            lbValue else_val = lb_emit_conv(p, lb_build_expr(p, else_expr), type);
            return lb_emit_select(p, has_value, then_val, else_val);
        }
    }
    // ... existing branch+phi path ...
```

### Why Only Trivial Else

The `lhs` value is always available (it was computed by `lb_emit_try_lhs_rhs`), so
evaluating it unconditionally is free. The `else_expr` might have side effects (e.g.,
`x or_else do_something()`), so it can only be unconditionally evaluated if trivial.

We do NOT need to check whether `lhs` is trivial — it has already been computed and
is just a value in a register.

### Safety

When `has_value` is true, the result is `lhs` (the unwrapped value). When false, the
result is `else_val`. This matches the branch+phi semantics exactly, provided `else_val`
evaluation has no side effects (guaranteed by the triviality check).

### Risk

Low. The triviality check is the same conservative check used for ternary select.

---

## 8. Complete Slice SSA Value Path for Array and MultiPointer

### What

Extend `lb_build_slice_expr_value` to handle `Type_Array` and `Type_MultiPointer` source
types, so these cases produce SSA `insertvalue` instead of alloca+GEP+store+load.

### Current State

`lb_build_slice_expr_value` (lines 4870-4967) handles:
- `Type_Slice` → `lb_make_slice_value` (SSA)
- `Type_DynamicArray` → `lb_make_slice_value` (SSA)
- `Type_Basic` (string/string16) → `lb_make_string_value` (SSA)

Missing: `Type_Array` and `Type_MultiPointer` fall through to `lb_build_addr_slice_expr`
which uses `lb_fill_slice` (alloca path).

### Type_Array

The addr path (`llvm_backend_expr.cpp:5061-5082`) does:
```
elem = ptr_offset(array_elem(addr_get_ptr(addr)), low)
new_len = high - low
alloca slice → fill_slice(slice, elem, new_len)
```

The value path needs the *address* of the array to compute `array_elem`. This is the
key constraint: you cannot take the address of an SSA value. However,
`lb_build_slice_expr_value` receives the array as `base = lb_build_expr(p, se->expr)`,
which is a value.

For arrays, slicing requires a pointer to the array data (since the result slice points
into the array's memory). The current addr path gets this from `lb_addr_get_ptr(p, addr)`
where `addr` comes from `lb_build_addr(p, se->expr)`. The value path would need to call
`lb_address_from_load_or_generate_local(p, base)` to get a pointer — which creates an
alloca anyway, defeating the purpose.

**Conclusion: Type_Array cannot benefit from the SSA slice path.** The result slice
*must* point into addressable memory, and if the array value is in an SSA register,
it must be spilled to get a pointer. The addr path is already optimal for this case.

### Type_MultiPointer (with high bound → slice result)

When `se->high != nullptr`, the result is a slice `{ptr, len}`. The addr path
(`llvm_backend_expr.cpp:5043-5057`) does:
```
ptr = GEP(base, low)
len = high - low
alloca res → GEP res.0 → store ptr; GEP res.1 → store len
```

This can become:
```
ptr = GEP(base, low)
len = high - low
return lb_make_slice_value(p, slice_type, ptr_val, len_val)
```

The GEP and subtraction produce SSA values. The slice construction is a 2-field struct.

### Type_MultiPointer (without high bound → multi-pointer result)

When `se->high == nullptr`, the result is a multi-pointer (pointer offset), not a slice.
The addr path (`llvm_backend_expr.cpp:5038-5042`) stores the offset pointer to an alloca.
This is a single-value store, not an aggregate construction. It could return the pointer
directly as an SSA value, but this requires the caller to expect an `lbValue` instead of
an `lbAddr`. Since `lb_build_addr_slice_expr` returns `lbAddr` and some callers may
need the address, leave this case in the addr path.

### Implementation

Add `Type_MultiPointer` (with high bound) to `lb_build_slice_expr_value`. In the
`lb_build_expr` dispatch for `SliceExpr`, route multi-pointer-to-slice cases to the
value path:

```cpp
case_ast_node(se, SliceExpr, expr);
    Type *result_type = type_of_expr(expr);
    if (is_type_slice(result_type) || is_type_string(result_type)) {
        Type *source_type = base_type(type_of_expr(se->expr));
        if (is_type_pointer(source_type)) {
            source_type = base_type(type_deref(source_type));
        }
        // Array slicing needs addressable memory — use addr path
        if (source_type->kind != Type_Array) {
            return lb_build_slice_expr_value(p, expr);
        }
    }
    return lb_addr_load(p, lb_build_addr(p, expr));
case_end;
```

### Safety

The bounds checks and pointer arithmetic are identical. Only the result assembly changes
from alloca+GEP+store to `insertvalue`. The multi-pointer GEP produces a pointer value;
the subtraction produces an integer value. Both are valid `insertvalue` operands.

### Risk

Low. The new value path for multi-pointer slicing is structurally identical to the
existing slice/dynamic-array value paths.

---

## Implementation Order

The items are ordered by independence (can be committed and tested separately) and by
impact (highest-impact first):

| Step | Section | Summary | Impact |
|------|---------|---------|--------|
| 1 | §1 | `nounwind` on Odin-CC functions | High — affects every function |
| 2 | §2 | Complex/quaternion arithmetic SSA | Medium — common math operations |
| 3 | §3 | `any` construction SSA | Medium-high — every `fmt.println` arg |
| 4 | §4 | Complex/quaternion conversion SSA | Medium — 7 conversion paths |
| 5 | §5 | Conjugate SSA | Low-medium — less frequent |
| 6 | §8 | MultiPointer slice SSA | Low-medium — completes value path |
| 7 | §6 | Ternary select expansion | Medium — common conditional pattern |
| 8 | §7 | `or_else` select | Medium — idiomatic Odin pattern |

Each step is independently compilable and testable. Commit after each step passes
`make && odin test tests/core/normal`.

---

## Deferred / Out of Scope

### Reducing `lb_address_from_load_or_generate_local` Call Sites

The 56 call sites of `lb_address_from_load_or_generate_local` are individually reasonable
— each needs a pointer for a specific purpose (passing to `memcmp`, storing into `any`,
map operations, etc.). A bulk reduction would require changing the APIs of downstream
consumers to accept SSA values, which is a much larger refactor. The specific cases
addressed in §3 (any construction) reduce the impact where it matters most.

### Lazy Parameter Spilling

The current pattern (alloca for every direct parameter, with SSA bypass via
`direct_parameters` map) works correctly and LLVM's mem2reg eliminates the dead allocas.
Making this lazy (only spill when address is taken) would require tracking address-taken
status per entity during codegen, which is complex for marginal benefit. The existing
`direct_parameters` bypass already avoids the load on every read. The alloca itself is
a single instruction that mem2reg removes in O(1).

### Compound Literal Zero-Init Elimination

Removing the unconditional `zero_init=true` in `lb_build_addr_compound_lit` requires
proving that every field is explicitly initialized — which depends on the frontend's
completeness checking. The current zero-init is a safety net that prevents undefined
behavior from uninitialized padding bytes in struct comparisons. The cost is one `memset`
per compound literal. Eliminating it requires either:
- Proving all fields are written (complex frontend analysis), or
- Proving the struct has no padding (already handled by `lb_add_local`'s padding check)

Not worth the risk for the marginal benefit.

### `memory(...)` and `willreturn` Attributes

Adding `memory(none)` / `memory(read)` / `willreturn` to user functions requires
interprocedural purity analysis (does the function write to memory? does it always
terminate?). The Odin frontend does not currently compute this information. Building
such an analysis is a significant undertaking better done as a standalone feature.
`nounwind` (§1) is the low-hanging fruit that enables LLVM to infer some of these
properties on its own.

---

## Verification Plan

After all changes:

1. `make` — debug build compiles
2. `make release` — release build compiles
3. `odin test tests/core/normal` — core tests pass
4. `odin run tests/core/test_comp.odin -file` — #comp tests pass
5. `bash tests/core/test_comp_errors.sh ./odin` — #comp error tests pass
6. Manual IR inspection: compile a small program using complex arithmetic, `any`,
   `or_else`, and ternary expressions. Verify with `odin build -file foo.odin
   -build-mode:llvm-ir` that the IR uses `insertvalue` instead of alloca+GEP+store
   and that `nounwind` appears on Odin-CC function definitions.
