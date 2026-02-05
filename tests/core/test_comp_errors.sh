#!/bin/bash
# Test that #comp correctly rejects impure and invalid programs.
# Each test case is a small Odin file that should FAIL to compile.

set -e
ODIN="./odin"
TMPDIR=$(mktemp -d)
trap "rm -rf $TMPDIR" EXIT

passed=0
failed=0

expect_error() {
    local name="$1"
    local code="$2"
    local expected_msg="$3"

    local file="$TMPDIR/${name}.odin"
    echo "$code" > "$file"

    if output=$($ODIN build "$file" -file 2>&1); then
        echo "FAIL: $name — expected compilation error but succeeded"
        rm -f "${file%.odin}"
        failed=$((failed + 1))
        return
    fi
    rm -f "${file%.odin}"

    if [ -n "$expected_msg" ]; then
        if echo "$output" | grep -qi "$expected_msg"; then
            echo "  OK: $name"
            passed=$((passed + 1))
        else
            echo "FAIL: $name — error message didn't contain '$expected_msg'"
            echo "  got: $output"
            failed=$((failed + 1))
        fi
    else
        echo "  OK: $name (compilation failed as expected)"
        passed=$((passed + 1))
    fi
}

echo "=== #comp error rejection tests ==="
echo ""

# --- Purity violations ---

expect_error "address_of" '
package test
bad :: proc() -> i32 { x: i32 = 5; _ = &x; return 1 }
x := #comp bad()
' "not pure"

expect_error "global_mutable" '
package test
g: i32 = 0
bad :: proc() -> i32 { return g }
x := #comp bad()
' "not pure"

expect_error "pointer_return" '
package test
bad :: proc() -> ^i32 { x: i32 = 5; return &x }
x := #comp bad()
' "not allowed"

expect_error "slice_return" '
package test
bad :: proc() -> []i32 { return nil }
x := #comp bad()
' "not allowed"

expect_error "dynamic_array_return" '
package test
bad :: proc() -> [dynamic]i32 { return nil }
x := #comp bad()
' "not allowed"

expect_error "map_return" '
package test
bad :: proc() -> map[i32]i32 { return nil }
x := #comp bad()
' "not allowed"

expect_error "string_return" '
package test
bad :: proc() -> string { return "hello" }
x := #comp bad()
' "not allowed"

expect_error "context_access" '
package test
bad :: proc() -> i32 { _ = context; return 1 }
x := #comp bad()
' "not pure"

expect_error "pointer_param" '
package test
bad :: proc(p: ^i32) -> i32 { return 0 }
x := #comp bad(nil)
' ""

expect_error "slice_param" '
package test
bad :: proc(s: []i32) -> i32 { return 0 }
x := #comp bad(nil)
' ""

expect_error "transmute_usage" '
package test
bad :: proc() -> i32 { x: f32 = 1.0; return transmute(i32)x }
x := #comp bad()
' "not pure"

# --- Type restrictions ---

expect_error "int_return" '
package test
bad :: proc() -> int { return 42 }
x := #comp bad()
' "not allowed"

expect_error "uint_return" '
package test
bad :: proc() -> uint { return 42 }
x := #comp bad()
' "not allowed"

# --- Must be a named procedure ---

expect_error "not_a_proc" '
package test
x := #comp 42
' ""

# --- No return value ---

expect_error "void_return" '
package test
noop :: proc() { }
x := #comp noop()
' ""

# --- Impurity through call chain ---

expect_error "impure_callee" '
package test
inner :: proc() -> i32 { _ = context; return 1 }
outer :: proc() -> i32 { return inner() }
x := #comp outer()
' "not pure"

# --- Deref is impure ---

expect_error "deref_expr" '
package test
bad :: proc() -> i32 {
	x: i32 = 5
	p := &x
	return p^
}
x := #comp bad()
' "not pure"

# --- Dynamic array in struct ---

expect_error "struct_with_dyn_array" '
package test
Bad :: struct { data: [dynamic]i32 }
make_bad :: proc() -> Bad { return Bad{} }
x := #comp make_bad()
' "not allowed"

# --- Proc type parameter ---

expect_error "proc_type_param" '
package test
bad :: proc(f: proc() -> i32) -> i32 { return 0 }
x := #comp bad(nil)
' ""

# --- Non-constant argument ---

expect_error "comp_runtime_arg" '
package test
double :: proc(x: i32) -> i32 { return x * 2 }
get_val :: proc() -> i32 { return 21 }
main :: proc() { x := #comp double(get_val()); _ = x }
' "not a compile-time constant"

# --- Argument type not comp-compatible ---

expect_error "comp_slice_arg" '
package test
sum_slice :: proc(s: []i32) -> i32 { return 0 }
x := #comp sum_slice(nil)
' "not allowed"

expect_error "comp_pointer_arg" '
package test
deref :: proc(p: ^i32) -> i32 { return 0 }
x := #comp deref(nil)
' "not allowed"

# --- Raw union struct ---

expect_error "raw_union_return" '
package test
RU :: struct #raw_union { a: i32, b: f32 }
bad :: proc() -> RU { return RU{} }
x := #comp bad()
' "not allowed"

# --- Additional type restrictions ---

expect_error "uintptr_return" '
package test
bad :: proc() -> uintptr { return 0 }
x := #comp bad()
' "not allowed"

expect_error "cstring_return" '
package test
bad :: proc() -> cstring { return nil }
x := #comp bad()
' "not allowed"

expect_error "union_return" '
package test
U :: union { i32, f32 }
bad :: proc() -> U { return U(i32(42)) }
x := #comp bad()
' "not allowed"

expect_error "enum_int_backing" '
package test
E :: enum int { A, B, C }
bad :: proc() -> E { return .A }
x := #comp bad()
' "not allowed"

expect_error "multiple_returns" '
package test
bad :: proc() -> (i32, bool) { return 42, true }
x := #comp bad()
' ""

# --- Struct field type restrictions (recursive) ---

expect_error "struct_with_pointer_field" '
package test
S :: struct { p: ^i32, v: i32 }
bad :: proc() -> S { return S{} }
x := #comp bad()
' "not allowed"

expect_error "struct_with_string_field" '
package test
S :: struct { name: string, id: i32 }
bad :: proc() -> S { return S{} }
x := #comp bad()
' "not allowed"

# --- Additional parameter type restrictions ---

expect_error "comp_string_param" '
package test
bad :: proc(s: string) -> i32 { return 0 }
x := #comp bad("hello")
' ""

expect_error "comp_int_param" '
package test
bad :: proc(x: int) -> i32 { return i32(x) }
x := #comp bad(42)
' ""

echo ""
echo "Results: $passed passed, $failed failed"
if [ $failed -gt 0 ]; then
    exit 1
fi
echo "All error rejection tests passed!"
