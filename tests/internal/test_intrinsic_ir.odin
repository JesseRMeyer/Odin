package test_internal

import "base:intrinsics"
import "core:testing"

// Helper to prevent constant folding
@(private = "file")
volatile :: proc(v: $T) -> T {
	x := v
	return x
}

// =============================================================================
// Integer min/max intrinsics (llvm.smin, llvm.smax, llvm.umin, llvm.umax)
// =============================================================================

@(test)
test_scalar_min_signed :: proc(t: ^testing.T) {
	testing.expect_value(t, min(volatile(i32(5)), volatile(i32(3))), i32(3))
	testing.expect_value(t, min(volatile(i32(-5)), volatile(i32(3))), i32(-5))
	testing.expect_value(t, min(volatile(i32(min(i32))), volatile(i32(0))), min(i32))
}

@(test)
test_scalar_max_signed :: proc(t: ^testing.T) {
	testing.expect_value(t, max(volatile(i32(5)), volatile(i32(3))), i32(5))
	testing.expect_value(t, max(volatile(i32(-5)), volatile(i32(3))), i32(3))
	testing.expect_value(t, max(volatile(i32(max(i32))), volatile(i32(0))), max(i32))
}

@(test)
test_scalar_min_unsigned :: proc(t: ^testing.T) {
	testing.expect_value(t, min(volatile(u32(5)), volatile(u32(3))), u32(3))
	testing.expect_value(t, min(volatile(u32(0)), volatile(u32(max(u32)))), u32(0))
}

@(test)
test_scalar_max_unsigned :: proc(t: ^testing.T) {
	testing.expect_value(t, max(volatile(u32(5)), volatile(u32(3))), u32(5))
	testing.expect_value(t, max(volatile(u32(0)), volatile(u32(max(u32)))), max(u32))
}

// =============================================================================
// Integer abs intrinsic (llvm.abs)
// =============================================================================

@(test)
test_scalar_abs :: proc(t: ^testing.T) {
	testing.expect_value(t, abs(volatile(i32(5))), i32(5))
	testing.expect_value(t, abs(volatile(i32(-5))), i32(5))
	testing.expect_value(t, abs(volatile(i32(0))), i32(0))
	// INT_MIN case: abs(INT_MIN) wraps to INT_MIN (is_int_min_poison = false)
	testing.expect_value(t, abs(volatile(min(i32))), min(i32))
}

// =============================================================================
// SIMD min/max (delegating to llvm.smin/smax/umin/umax)
// =============================================================================

@(test)
test_simd_min_signed :: proc(t: ^testing.T) {
	a := volatile(#simd[4]i32{5, -3, 7, -1})
	b := volatile(#simd[4]i32{3, -5, 2, 0})
	result := intrinsics.simd_min(a, b)
	testing.expect_value(t, result, #simd[4]i32{3, -5, 2, -1})
}

@(test)
test_simd_max_signed :: proc(t: ^testing.T) {
	a := volatile(#simd[4]i32{5, -3, 7, -1})
	b := volatile(#simd[4]i32{3, -5, 2, 0})
	result := intrinsics.simd_max(a, b)
	testing.expect_value(t, result, #simd[4]i32{5, -3, 7, 0})
}

@(test)
test_simd_min_unsigned :: proc(t: ^testing.T) {
	a := volatile(#simd[4]u32{5, 3, 7, 1})
	b := volatile(#simd[4]u32{3, 5, 2, 0})
	result := intrinsics.simd_min(a, b)
	testing.expect_value(t, result, #simd[4]u32{3, 3, 2, 0})
}

@(test)
test_simd_max_unsigned :: proc(t: ^testing.T) {
	a := volatile(#simd[4]u32{5, 3, 7, 1})
	b := volatile(#simd[4]u32{3, 5, 2, 0})
	result := intrinsics.simd_max(a, b)
	testing.expect_value(t, result, #simd[4]u32{5, 5, 7, 1})
}

// =============================================================================
// SIMD abs (llvm.abs for signed, identity for unsigned)
// =============================================================================

@(test)
test_simd_abs_signed :: proc(t: ^testing.T) {
	a := volatile(#simd[4]i32{5, -3, 0, -7})
	result := intrinsics.simd_abs(a)
	testing.expect_value(t, result, #simd[4]i32{5, 3, 0, 7})
}

@(test)
test_simd_abs_signed_intmin :: proc(t: ^testing.T) {
	a := volatile(#simd[4]i32{min(i32), max(i32), 0, -1})
	result := intrinsics.simd_abs(a)
	// abs(INT_MIN) wraps to INT_MIN
	testing.expect_value(t, result, #simd[4]i32{min(i32), max(i32), 0, 1})
}

@(test)
test_simd_abs_unsigned :: proc(t: ^testing.T) {
	// Unsigned abs should be identity
	a := volatile(#simd[4]u32{5, 3, 0, 7})
	result := intrinsics.simd_abs(a)
	testing.expect_value(t, result, #simd[4]u32{5, 3, 0, 7})
}

// =============================================================================
// SIMD hadd (uses poison instead of undef for shuffle operand)
// These are additional tests beyond the existing ones in test_simd_intrinsics.odin
// =============================================================================

@(test)
test_simd_hadd_i32_ir :: proc(t: ^testing.T) {
	// Additional test to verify poison doesn't break hadd
	a := volatile(#simd[4]i32{10, 20, 30, 40})
	result := intrinsics.simd_hadd(a)
	testing.expect_value(t, result, #simd[2]i32{30, 70})
}

@(test)
test_simd_hsub_i32_ir :: proc(t: ^testing.T) {
	// Additional test to verify poison doesn't break hsub
	a := volatile(#simd[4]i32{100, 30, 50, 10})
	result := intrinsics.simd_hsub(a)
	testing.expect_value(t, result, #simd[2]i32{70, 40})
}
