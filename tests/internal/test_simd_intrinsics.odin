package test_internal

import "base:intrinsics"
import "core:testing"
import "core:math"

// Helper: volatile load to prevent constant folding
@(private = "file")
vload :: #force_inline proc "contextless" (p: ^$T) -> T {
	return intrinsics.volatile_load(p)
}

// =============================================================================
// simd_rem - Integer remainder
// =============================================================================

@(test)
test_simd_rem_i32 :: proc(t: ^testing.T) {
	a := vload(&(#simd[4]i32{7, -7, 7, -7}))
	b := vload(&(#simd[4]i32{3, 3, -3, -3}))
	result := intrinsics.simd_rem(a, b)
	testing.expect_value(t, result, #simd[4]i32{1, -1, 1, -1})
}

@(test)
test_simd_rem_u32 :: proc(t: ^testing.T) {
	a := vload(&(#simd[4]u32{10, 17, 25, 100}))
	b := vload(&(#simd[4]u32{3, 5, 7, 11}))
	result := intrinsics.simd_rem(a, b)
	testing.expect_value(t, result, #simd[4]u32{1, 2, 4, 1})
}

// =============================================================================
// simd_div - Integer division (now enabled)
// =============================================================================

@(test)
test_simd_div_i32 :: proc(t: ^testing.T) {
	a := vload(&(#simd[4]i32{10, -10, 10, -10}))
	b := vload(&(#simd[4]i32{3, 3, -3, -3}))
	result := intrinsics.simd_div(a, b)
	testing.expect_value(t, result, #simd[4]i32{3, -3, -3, 3})
}

@(test)
test_simd_div_u32 :: proc(t: ^testing.T) {
	a := vload(&(#simd[4]u32{100, 50, 25, 10}))
	b := vload(&(#simd[4]u32{10, 7, 5, 3}))
	result := intrinsics.simd_div(a, b)
	testing.expect_value(t, result, #simd[4]u32{10, 7, 5, 3})
}

@(test)
test_simd_div_f32 :: proc(t: ^testing.T) {
	a := vload(&(#simd[4]f32{2.0, 9.0, -6.0, 1.0}))
	b := vload(&(#simd[4]f32{0.5, 3.0, 2.0, -4.0}))
	result := intrinsics.simd_div(a, b)
	testing.expect_value(t, result, #simd[4]f32{4.0, 3.0, -3.0, -0.25})
}

// =============================================================================
// simd_bit_not - Bitwise complement
// =============================================================================

@(test)
test_simd_bit_not_i32 :: proc(t: ^testing.T) {
	a := vload(&(#simd[4]i32{0, -1, 0x0F0F0F0F, 0x12345678}))
	result := intrinsics.simd_bit_not(a)
	testing.expect_value(t, result, #simd[4]i32{-1, 0, -252645136, -305419897})
}

@(test)
test_simd_bit_not_u8 :: proc(t: ^testing.T) {
	a := vload(&(#simd[4]u8{0x00, 0xFF, 0xAA, 0x55}))
	result := intrinsics.simd_bit_not(a)
	testing.expect_value(t, result, #simd[4]u8{0xFF, 0x00, 0x55, 0xAA})
}

// =============================================================================
// simd_copysign - IEEE 754 copysign
// =============================================================================

@(test)
test_simd_copysign_f32 :: proc(t: ^testing.T) {
	mag := vload(&(#simd[4]f32{1.0, 2.0, 3.0, 4.0}))
	sgn := vload(&(#simd[4]f32{-1.0, 1.0, -1.0, 1.0}))
	result := intrinsics.simd_copysign(mag, sgn)
	testing.expect_value(t, result, #simd[4]f32{-1.0, 2.0, -3.0, 4.0})
}

@(test)
test_simd_copysign_zero :: proc(t: ^testing.T) {
	// Copysign should work with signed zeros
	mag := vload(&(#simd[4]f32{1.0, 1.0, 0.0, 0.0}))
	sgn := vload(&(#simd[4]f32{0.0, -0.0, -0.0, 0.0}))
	result := intrinsics.simd_copysign(mag, sgn)
	// Check signs via bit representation
	arr := transmute([4]u32)result
	testing.expect(t, (arr[0] & 0x80000000) == 0, "lane 0 should be positive")
	testing.expect(t, (arr[1] & 0x80000000) != 0, "lane 1 should be negative")
	testing.expect(t, (arr[2] & 0x80000000) != 0, "lane 2 should be negative zero")
	testing.expect(t, (arr[3] & 0x80000000) == 0, "lane 3 should be positive zero")
}

// =============================================================================
// simd_rcp / simd_rcp_fast - Reciprocal
// =============================================================================

@(test)
test_simd_rcp_f32 :: proc(t: ^testing.T) {
	a := vload(&(#simd[4]f32{1.0, 2.0, 4.0, 0.5}))
	result := intrinsics.simd_rcp(a)
	testing.expect_value(t, result, #simd[4]f32{1.0, 0.5, 0.25, 2.0})
}

@(test)
test_simd_rcp_fast_f32 :: proc(t: ^testing.T) {
	a := vload(&(#simd[4]f32{1.0, 2.0, 4.0, 0.5}))
	result := intrinsics.simd_rcp_fast(a)
	// Fast version may not be exact, check within tolerance
	expected := [4]f32{1.0, 0.5, 0.25, 2.0}
	arr := transmute([4]f32)result
	for i in 0 ..< 4 {
		diff := abs(arr[i] - expected[i])
		rel_err := diff / abs(expected[i])
		testing.expect(t, rel_err < 0.01, "rcp_fast should be within 1% of exact")
	}
}

@(test)
test_simd_rcp_f64 :: proc(t: ^testing.T) {
	a := vload(&(#simd[2]f64{1.0, 8.0}))
	result := intrinsics.simd_rcp(a)
	testing.expect_value(t, result, #simd[2]f64{1.0, 0.125})
}

// =============================================================================
// simd_rsqrt / simd_rsqrt_fast - Reciprocal square root
// =============================================================================

@(test)
test_simd_rsqrt_f32 :: proc(t: ^testing.T) {
	a := vload(&(#simd[4]f32{1.0, 4.0, 16.0, 0.25}))
	result := intrinsics.simd_rsqrt(a)
	testing.expect_value(t, result, #simd[4]f32{1.0, 0.5, 0.25, 2.0})
}

@(test)
test_simd_rsqrt_fast_f32 :: proc(t: ^testing.T) {
	a := vload(&(#simd[4]f32{1.0, 4.0, 16.0, 0.25}))
	result := intrinsics.simd_rsqrt_fast(a)
	// Fast version may not be exact, check within tolerance
	expected := [4]f32{1.0, 0.5, 0.25, 2.0}
	arr := transmute([4]f32)result
	for i in 0 ..< 4 {
		diff := abs(arr[i] - expected[i])
		rel_err := diff / abs(expected[i])
		testing.expect(t, rel_err < 0.01, "rsqrt_fast should be within 1% of exact")
	}
}

// =============================================================================
// simd_sext - Sign extension
// =============================================================================

@(test)
test_simd_sext_i16_to_i32 :: proc(t: ^testing.T) {
	a := vload(&(#simd[4]i16{100, -100, 32767, -32768}))
	result := intrinsics.simd_sext(a, #simd[4]i32)
	testing.expect_value(t, result, #simd[4]i32{100, -100, 32767, -32768})
}

@(test)
test_simd_sext_i8_to_i32 :: proc(t: ^testing.T) {
	a := vload(&(#simd[4]i8{1, -1, 127, -128}))
	result := intrinsics.simd_sext(a, #simd[4]i32)
	testing.expect_value(t, result, #simd[4]i32{1, -1, 127, -128})
}

// =============================================================================
// simd_zext - Zero extension
// =============================================================================

@(test)
test_simd_zext_u16_to_u32 :: proc(t: ^testing.T) {
	a := vload(&(#simd[4]u16{100, 200, 65535, 0}))
	result := intrinsics.simd_zext(a, #simd[4]u32)
	testing.expect_value(t, result, #simd[4]u32{100, 200, 65535, 0})
}

@(test)
test_simd_zext_u8_to_u32 :: proc(t: ^testing.T) {
	a := vload(&(#simd[4]u8{0, 127, 128, 255}))
	result := intrinsics.simd_zext(a, #simd[4]u32)
	testing.expect_value(t, result, #simd[4]u32{0, 127, 128, 255})
}

// =============================================================================
// simd_narrow - Truncation (no saturation)
// =============================================================================

@(test)
test_simd_narrow_i32_to_i16 :: proc(t: ^testing.T) {
	a := vload(&(#simd[4]i32{100, -100, 0x12345678, 0}))
	result := intrinsics.simd_narrow(a, #simd[4]i16)
	// 0x12345678 truncates to 0x5678 = 22136
	testing.expect_value(t, result, #simd[4]i16{100, -100, 22136, 0})
}

@(test)
test_simd_narrow_i32_to_i8 :: proc(t: ^testing.T) {
	a := vload(&(#simd[4]i32{50, -50, 0x123, 0xABCD}))
	result := intrinsics.simd_narrow(a, #simd[4]i8)
	// 0x123 truncates to 0x23 = 35, 0xABCD truncates to 0xCD = -51
	testing.expect_value(t, result, #simd[4]i8{50, -50, 35, -51})
}

// =============================================================================
// simd_narrow_sat - Signed saturating narrow
// =============================================================================

@(test)
test_simd_narrow_sat_i32_to_i16 :: proc(t: ^testing.T) {
	a := vload(&(#simd[4]i32{100, -100, 50000, -50000}))
	result := intrinsics.simd_narrow_sat(a, #simd[4]i16)
	// 50000 clamps to 32767, -50000 clamps to -32768
	testing.expect_value(t, result, #simd[4]i16{100, -100, 32767, -32768})
}

@(test)
test_simd_narrow_sat_i32_to_i8 :: proc(t: ^testing.T) {
	a := vload(&(#simd[4]i32{50, -50, 200, -200}))
	result := intrinsics.simd_narrow_sat(a, #simd[4]i8)
	// 200 clamps to 127, -200 clamps to -128
	testing.expect_value(t, result, #simd[4]i8{50, -50, 127, -128})
}

@(test)
test_simd_narrow_sat_boundary :: proc(t: ^testing.T) {
	// Test exact boundary values
	a := vload(&(#simd[4]i32{127, 128, -128, -129}))
	result := intrinsics.simd_narrow_sat(a, #simd[4]i8)
	testing.expect_value(t, result, #simd[4]i8{127, 127, -128, -128})
}

@(test)
test_simd_narrow_sat_unsigned_source :: proc(t: ^testing.T) {
	// Test unsigned source with signed saturation (the bug case fixed)
	// Unsigned values should clamp to the positive bound, never the negative bound
	a := vload(&(#simd[4]u16{300, 50, 200, 0}))
	result := intrinsics.simd_narrow_sat(a, #simd[4]i8)
	// 300 and 200 are > 127, so they clamp to 127 (not -128!)
	// 50 and 0 are in range, so they pass through
	testing.expect_value(t, result, #simd[4]i8{127, 50, 127, 0})
}

// =============================================================================
// simd_narrow_usat - Unsigned saturating narrow
// =============================================================================

@(test)
test_simd_narrow_usat_i32_to_u16 :: proc(t: ^testing.T) {
	a := vload(&(#simd[4]i32{100, -100, 100000, 65535}))
	result := intrinsics.simd_narrow_usat(a, #simd[4]u16)
	// -100 clamps to 0, 100000 clamps to 65535
	testing.expect_value(t, result, #simd[4]u16{100, 0, 65535, 65535})
}

@(test)
test_simd_narrow_usat_i32_to_u8 :: proc(t: ^testing.T) {
	a := vload(&(#simd[4]i32{50, -50, 300, 255}))
	result := intrinsics.simd_narrow_usat(a, #simd[4]u8)
	// -50 clamps to 0, 300 clamps to 255
	testing.expect_value(t, result, #simd[4]u8{50, 0, 255, 255})
}

@(test)
test_simd_narrow_usat_from_unsigned :: proc(t: ^testing.T) {
	// Unsigned source, no negatives to clamp
	a := vload(&(#simd[4]u32{50, 200, 300, 1000}))
	result := intrinsics.simd_narrow_usat(a, #simd[4]u8)
	testing.expect_value(t, result, #simd[4]u8{50, 200, 255, 255})
}

// =============================================================================
// simd_ftoi - Float to integer (saturating)
// =============================================================================

@(test)
test_simd_ftoi_f32_to_i32 :: proc(t: ^testing.T) {
	a := vload(&(#simd[4]f32{1.9, -1.9, 100.5, -100.5}))
	result := intrinsics.simd_ftoi(a, #simd[4]i32)
	// Truncation toward zero
	testing.expect_value(t, result, #simd[4]i32{1, -1, 100, -100})
}

@(test)
test_simd_ftoi_saturation :: proc(t: ^testing.T) {
	// Test saturation at integer bounds
	a := vload(&(#simd[4]f32{3.0e9, -3.0e9, 1.0e20, -1.0e20}))
	result := intrinsics.simd_ftoi(a, #simd[4]i32)
	testing.expect_value(t, result, #simd[4]i32{max(i32), min(i32), max(i32), min(i32)})
}

@(test)
test_simd_ftoi_nan :: proc(t: ^testing.T) {
	// NaN should map to 0
	nan := math.nan_f32()
	nan_vec := #simd[4]f32{nan, 1.0, nan, -1.0}
	a := vload(&nan_vec)
	result := intrinsics.simd_ftoi(a, #simd[4]i32)
	arr := transmute([4]i32)result
	testing.expect_value(t, arr[0], 0)
	testing.expect_value(t, arr[1], 1)
	testing.expect_value(t, arr[2], 0)
	testing.expect_value(t, arr[3], -1)
}

@(test)
test_simd_ftoi_unsigned :: proc(t: ^testing.T) {
	a := vload(&(#simd[4]f32{1.9, 100.5, 0.0, 255.9}))
	result := intrinsics.simd_ftoi(a, #simd[4]u32)
	testing.expect_value(t, result, #simd[4]u32{1, 100, 0, 255})
}

// =============================================================================
// simd_itof - Integer to float
// =============================================================================

@(test)
test_simd_itof_i32_to_f32 :: proc(t: ^testing.T) {
	a := vload(&(#simd[4]i32{1, -1, 100, -100}))
	result := intrinsics.simd_itof(a, #simd[4]f32)
	testing.expect_value(t, result, #simd[4]f32{1.0, -1.0, 100.0, -100.0})
}

@(test)
test_simd_itof_u32_to_f32 :: proc(t: ^testing.T) {
	a := vload(&(#simd[4]u32{0, 1, 100, 1000}))
	result := intrinsics.simd_itof(a, #simd[4]f32)
	testing.expect_value(t, result, #simd[4]f32{0.0, 1.0, 100.0, 1000.0})
}

// =============================================================================
// simd_fpext - Float precision extension
// =============================================================================

@(test)
test_simd_fpext_f32_to_f64 :: proc(t: ^testing.T) {
	a := vload(&(#simd[2]f32{1.5, -2.5}))
	result := intrinsics.simd_fpext(a, #simd[2]f64)
	testing.expect_value(t, result, #simd[2]f64{1.5, -2.5})
}

// =============================================================================
// simd_fptrunc - Float precision truncation
// =============================================================================

@(test)
test_simd_fptrunc_f64_to_f32 :: proc(t: ^testing.T) {
	a := vload(&(#simd[2]f64{1.5, -2.5}))
	result := intrinsics.simd_fptrunc(a, #simd[2]f32)
	testing.expect_value(t, result, #simd[2]f32{1.5, -2.5})
}

// =============================================================================
// simd_hadd - Horizontal pairwise add
// =============================================================================

@(test)
test_simd_hadd_i32 :: proc(t: ^testing.T) {
	a := vload(&(#simd[4]i32{1, 2, 3, 4}))
	result := intrinsics.simd_hadd(a)
	// [1+2, 3+4] = [3, 7]
	testing.expect_value(t, result, #simd[2]i32{3, 7})
}

@(test)
test_simd_hadd_f32 :: proc(t: ^testing.T) {
	a := vload(&(#simd[4]f32{1.0, 2.0, 3.0, 4.0}))
	result := intrinsics.simd_hadd(a)
	testing.expect_value(t, result, #simd[2]f32{3.0, 7.0})
}

@(test)
test_simd_hadd_8_lanes :: proc(t: ^testing.T) {
	a := vload(&(#simd[8]i32{1, 2, 3, 4, 5, 6, 7, 8}))
	result := intrinsics.simd_hadd(a)
	// [1+2, 3+4, 5+6, 7+8] = [3, 7, 11, 15]
	testing.expect_value(t, result, #simd[4]i32{3, 7, 11, 15})
}

@(test)
test_simd_hadd_iterative_sum :: proc(t: ^testing.T) {
	// Demonstrate iterative reduction for full horizontal sum
	a := vload(&(#simd[4]i32{1, 2, 3, 4}))
	h1 := intrinsics.simd_hadd(a) // [3, 7]
	h2 := intrinsics.simd_hadd(h1) // [10]
	arr := transmute([1]i32)h2
	testing.expect_value(t, arr[0], 10) // Sum of all elements
}

// =============================================================================
// simd_hsub - Horizontal pairwise subtract
// =============================================================================

@(test)
test_simd_hsub_i32 :: proc(t: ^testing.T) {
	a := vload(&(#simd[4]i32{4, 1, 6, 2}))
	result := intrinsics.simd_hsub(a)
	// [4-1, 6-2] = [3, 4]
	testing.expect_value(t, result, #simd[2]i32{3, 4})
}

@(test)
test_simd_hsub_f32 :: proc(t: ^testing.T) {
	a := vload(&(#simd[4]f32{5.0, 2.0, 8.0, 3.0}))
	result := intrinsics.simd_hsub(a)
	testing.expect_value(t, result, #simd[2]f32{3.0, 5.0})
}

// =============================================================================
// byte_swap for SIMD vectors
// =============================================================================

@(test)
test_byte_swap_simd_i32 :: proc(t: ^testing.T) {
	a := vload(&(#simd[4]i32{0x12345678, 0x11223344, 0x01020304, 0x00000001}))
	result := intrinsics.byte_swap(a)
	testing.expect_value(t, result, #simd[4]i32{0x78563412, 0x44332211, 0x04030201, 0x01000000})
}

@(test)
test_byte_swap_simd_u16 :: proc(t: ^testing.T) {
	a := vload(&(#simd[4]u16{0x1234, 0xABCD, 0x0100, 0xFF00}))
	result := intrinsics.byte_swap(a)
	testing.expect_value(t, result, #simd[4]u16{0x3412, 0xCDAB, 0x0001, 0x00FF})
}

@(test)
test_byte_swap_simd_u64 :: proc(t: ^testing.T) {
	a := vload(&(#simd[2]u64{0x0102030405060708, 0x1100FFEEDDCCBBAA}))
	result := intrinsics.byte_swap(a)
	testing.expect_value(t, result, #simd[2]u64{0x0807060504030201, 0xAABBCCDDEEFF0011})
}

// =============================================================================
// simd_abs - Test the fixed float abs (uses llvm.fabs now)
// =============================================================================

@(test)
test_simd_abs_f32 :: proc(t: ^testing.T) {
	a := vload(&(#simd[4]f32{-1.0, 2.0, -3.0, 0.0}))
	result := intrinsics.simd_abs(a)
	testing.expect_value(t, result, #simd[4]f32{1.0, 2.0, 3.0, 0.0})
}

@(test)
test_simd_abs_negative_zero :: proc(t: ^testing.T) {
	// -0.0 should become +0.0
	a := vload(&(#simd[4]f32{-0.0, -0.0, 0.0, 0.0}))
	result := intrinsics.simd_abs(a)
	arr := transmute([4]u32)result
	// All results should be +0.0 (no sign bit set)
	for i in 0 ..< 4 {
		testing.expect(t, (arr[i] & 0x80000000) == 0, "abs should produce positive zero")
	}
}

@(test)
test_simd_abs_nan :: proc(t: ^testing.T) {
	// abs(NaN) should be NaN (with positive sign bit cleared)
	nan := math.nan_f32()
	neg_nan := -nan
	nan_vec := #simd[4]f32{nan, neg_nan, 1.0, -1.0}
	a := vload(&nan_vec)
	result := intrinsics.simd_abs(a)
	arr := transmute([4]f32)result
	// Check that NaN results are still NaN
	testing.expect(t, arr[0] != arr[0], "abs(NaN) should be NaN")
	testing.expect(t, arr[1] != arr[1], "abs(-NaN) should be NaN")
	testing.expect_value(t, arr[2], 1.0)
	testing.expect_value(t, arr[3], 1.0)
}

@(test)
test_simd_abs_i32 :: proc(t: ^testing.T) {
	a := vload(&(#simd[4]i32{-1, 2, -3, 0}))
	result := intrinsics.simd_abs(a)
	testing.expect_value(t, result, #simd[4]i32{1, 2, 3, 0})
}

// =============================================================================
// Additional edge case tests
// =============================================================================

// --- rcp/rsqrt edge cases ---

@(test)
test_simd_rcp_zero :: proc(t: ^testing.T) {
	// 1/0 should produce infinity
	a := vload(&(#simd[4]f32{0.0, -0.0, 1.0, -1.0}))
	result := intrinsics.simd_rcp(a)
	arr := transmute([4]f32)result
	testing.expect(t, math.is_inf(arr[0], 1), "1/+0 should be +inf")
	testing.expect(t, math.is_inf(arr[1], -1), "1/-0 should be -inf")
	testing.expect_value(t, arr[2], 1.0)
	testing.expect_value(t, arr[3], -1.0)
}

@(test)
test_simd_rsqrt_edge_cases :: proc(t: ^testing.T) {
	// rsqrt(0) = inf, rsqrt(negative) = NaN
	neg := f32(-1.0)
	a := vload(&(#simd[4]f32{0.0, neg, math.inf_f32(1), 1.0}))
	result := intrinsics.simd_rsqrt(a)
	arr := transmute([4]f32)result
	testing.expect(t, math.is_inf(arr[0], 1), "rsqrt(0) should be +inf")
	testing.expect(t, math.is_nan(arr[1]), "rsqrt(negative) should be NaN")
	testing.expect_value(t, arr[2], 0.0) // rsqrt(inf) = 0
	testing.expect_value(t, arr[3], 1.0)
}

// --- ftoi edge cases ---

@(test)
test_simd_ftoi_infinity :: proc(t: ^testing.T) {
	// Infinity should saturate to integer bounds
	pos_inf := math.inf_f32(1)
	neg_inf := math.inf_f32(-1)
	a := vload(&(#simd[4]f32{pos_inf, neg_inf, 0.0, 1.0}))
	result := intrinsics.simd_ftoi(a, #simd[4]i32)
	testing.expect_value(t, result, #simd[4]i32{max(i32), min(i32), 0, 1})
}

@(test)
test_simd_ftoi_unsigned_negative :: proc(t: ^testing.T) {
	// Negative floats to unsigned should saturate to 0
	a := vload(&(#simd[4]f32{-1.0, -100.0, 0.0, 1.0}))
	result := intrinsics.simd_ftoi(a, #simd[4]u32)
	testing.expect_value(t, result, #simd[4]u32{0, 0, 0, 1})
}

@(test)
test_simd_ftoi_unsigned_large :: proc(t: ^testing.T) {
	// Large positive floats to unsigned should saturate to max
	a := vload(&(#simd[4]f32{5.0e9, 1.0e20, 100.0, 0.0}))
	result := intrinsics.simd_ftoi(a, #simd[4]u32)
	arr := transmute([4]u32)result
	testing.expect_value(t, arr[0], max(u32))
	testing.expect_value(t, arr[1], max(u32))
	testing.expect_value(t, arr[2], 100)
	testing.expect_value(t, arr[3], 0)
}

// --- copysign edge cases ---

@(test)
test_simd_copysign_infinity :: proc(t: ^testing.T) {
	pos_inf := math.inf_f32(1)
	neg_inf := math.inf_f32(-1)
	mag := vload(&(#simd[4]f32{pos_inf, pos_inf, 1.0, 1.0}))
	sgn := vload(&(#simd[4]f32{1.0, -1.0, pos_inf, neg_inf}))
	result := intrinsics.simd_copysign(mag, sgn)
	arr := transmute([4]f32)result
	testing.expect(t, math.is_inf(arr[0], 1), "copysign(+inf, +) should be +inf")
	testing.expect(t, math.is_inf(arr[1], -1), "copysign(+inf, -) should be -inf")
	testing.expect_value(t, arr[2], 1.0)
	testing.expect_value(t, arr[3], -1.0)
}

@(test)
test_simd_copysign_nan :: proc(t: ^testing.T) {
	nan := math.nan_f32()
	mag := vload(&(#simd[4]f32{nan, nan, 1.0, 1.0}))
	sgn := vload(&(#simd[4]f32{1.0, -1.0, nan, -nan}))
	result := intrinsics.simd_copysign(mag, sgn)
	arr := transmute([4]f32)result
	// copysign(NaN, x) should be NaN with the sign of x
	testing.expect(t, math.is_nan(arr[0]), "copysign(NaN, +) should be NaN")
	testing.expect(t, math.is_nan(arr[1]), "copysign(NaN, -) should be NaN")
	// Check sign bits
	bits := transmute([4]u32)result
	testing.expect(t, (bits[0] & 0x80000000) == 0, "copysign(NaN, +) should have positive sign")
	testing.expect(t, (bits[1] & 0x80000000) != 0, "copysign(NaN, -) should have negative sign")
}

// --- abs edge cases ---

@(test)
test_simd_abs_int_min :: proc(t: ^testing.T) {
	// abs(INT_MIN) behavior - llvm.abs with poison=false wraps to INT_MIN
	// This is platform-defined but we test the actual behavior
	a := vload(&(#simd[4]i32{min(i32), max(i32), -1, 1}))
	result := intrinsics.simd_abs(a)
	arr := transmute([4]i32)result
	// abs(INT_MIN) wraps to INT_MIN (two's complement)
	testing.expect_value(t, arr[0], min(i32))
	testing.expect_value(t, arr[1], max(i32))
	testing.expect_value(t, arr[2], 1)
	testing.expect_value(t, arr[3], 1)
}

@(test)
test_simd_abs_f32_infinity :: proc(t: ^testing.T) {
	pos_inf := math.inf_f32(1)
	neg_inf := math.inf_f32(-1)
	a := vload(&(#simd[4]f32{pos_inf, neg_inf, 0.0, -0.0}))
	result := intrinsics.simd_abs(a)
	arr := transmute([4]f32)result
	testing.expect(t, math.is_inf(arr[0], 1), "abs(+inf) should be +inf")
	testing.expect(t, math.is_inf(arr[1], 1), "abs(-inf) should be +inf")
}

// --- hadd/hsub edge cases ---

@(test)
test_simd_hadd_2_lanes :: proc(t: ^testing.T) {
	// Minimum lane count
	a := vload(&(#simd[2]i32{100, 200}))
	result := intrinsics.simd_hadd(a)
	arr := transmute([1]i32)result
	testing.expect_value(t, arr[0], 300)
}

@(test)
test_simd_hsub_2_lanes :: proc(t: ^testing.T) {
	a := vload(&(#simd[2]i32{500, 200}))
	result := intrinsics.simd_hsub(a)
	arr := transmute([1]i32)result
	testing.expect_value(t, arr[0], 300)
}

@(test)
test_simd_hadd_negative :: proc(t: ^testing.T) {
	a := vload(&(#simd[4]i32{-10, 20, -30, -40}))
	result := intrinsics.simd_hadd(a)
	// [-10+20, -30+(-40)] = [10, -70]
	testing.expect_value(t, result, #simd[2]i32{10, -70})
}

// --- narrow_sat extended edge cases ---

@(test)
test_simd_narrow_sat_i64_to_i8 :: proc(t: ^testing.T) {
	// Test multi-step narrowing (64-bit to 8-bit)
	a := vload(&(#simd[2]i64{1000, -1000}))
	result := intrinsics.simd_narrow_sat(a, #simd[2]i8)
	testing.expect_value(t, result, #simd[2]i8{127, -128})
}

@(test)
test_simd_narrow_sat_extreme_values :: proc(t: ^testing.T) {
	// Test with i32 min/max
	a := vload(&(#simd[4]i32{max(i32), min(i32), 0, 1}))
	result := intrinsics.simd_narrow_sat(a, #simd[4]i16)
	testing.expect_value(t, result, #simd[4]i16{max(i16), min(i16), 0, 1})
}

@(test)
test_simd_narrow_usat_extreme_values :: proc(t: ^testing.T) {
	// Test with extreme negative and positive values
	a := vload(&(#simd[4]i32{min(i32), max(i32), -1, 256}))
	result := intrinsics.simd_narrow_usat(a, #simd[4]u8)
	// min(i32) clamps to 0, max(i32) clamps to 255, -1 clamps to 0, 256 clamps to 255
	testing.expect_value(t, result, #simd[4]u8{0, 255, 0, 255})
}

// --- sext/zext edge cases ---

@(test)
test_simd_sext_high_bit :: proc(t: ^testing.T) {
	// 0x80 as i8 is -128, should sign-extend to -128 as i32
	// 0x7F as i8 is 127, should sign-extend to 127 as i32
	a := vload(&(#simd[4]i8{-128, 127, -1, 0}))
	result := intrinsics.simd_sext(a, #simd[4]i32)
	testing.expect_value(t, result, #simd[4]i32{-128, 127, -1, 0})
}

@(test)
test_simd_zext_high_bit :: proc(t: ^testing.T) {
	// 0x80 as u8 is 128, should zero-extend to 128 as u32
	// 0xFF as u8 is 255, should zero-extend to 255 as u32
	a := vload(&(#simd[4]u8{0x80, 0x7F, 0xFF, 0}))
	result := intrinsics.simd_zext(a, #simd[4]u32)
	testing.expect_value(t, result, #simd[4]u32{128, 127, 255, 0})
}

// --- fpext/fptrunc edge cases ---

@(test)
test_simd_fpext_special_values :: proc(t: ^testing.T) {
	pos_inf := math.inf_f32(1)
	neg_inf := math.inf_f32(-1)
	nan := math.nan_f32()
	a := vload(&(#simd[4]f32{pos_inf, neg_inf, nan, -0.0}))
	result := intrinsics.simd_fpext(a, #simd[4]f64)
	arr := transmute([4]f64)result
	testing.expect(t, math.is_inf(arr[0], 1), "fpext(+inf) should be +inf")
	testing.expect(t, math.is_inf(arr[1], -1), "fpext(-inf) should be -inf")
	testing.expect(t, math.is_nan(arr[2]), "fpext(NaN) should be NaN")
	// Check -0.0 preserved
	bits := transmute([4]u64)result
	testing.expect(t, bits[3] == 0x8000000000000000, "fpext(-0) should preserve sign")
}

@(test)
test_simd_fptrunc_special_values :: proc(t: ^testing.T) {
	pos_inf := math.inf_f64(1)
	neg_inf := math.inf_f64(-1)
	nan := math.nan_f64()
	a := vload(&(#simd[4]f64{pos_inf, neg_inf, nan, -0.0}))
	result := intrinsics.simd_fptrunc(a, #simd[4]f32)
	arr := transmute([4]f32)result
	testing.expect(t, math.is_inf(arr[0], 1), "fptrunc(+inf) should be +inf")
	testing.expect(t, math.is_inf(arr[1], -1), "fptrunc(-inf) should be -inf")
	testing.expect(t, math.is_nan(arr[2]), "fptrunc(NaN) should be NaN")
	// Check -0.0 preserved
	bits := transmute([4]u32)result
	testing.expect(t, bits[3] == 0x80000000, "fptrunc(-0) should preserve sign")
}

// --- itof edge cases ---

@(test)
test_simd_itof_extreme_values :: proc(t: ^testing.T) {
	// Large integers may lose precision when converted to f32
	a := vload(&(#simd[4]i32{max(i32), min(i32), 0, 1}))
	result := intrinsics.simd_itof(a, #simd[4]f32)
	arr := transmute([4]f32)result
	// These won't be exact due to f32 precision limits, but should be close
	testing.expect(t, arr[0] > 2.0e9, "itof(max_i32) should be large positive")
	testing.expect(t, arr[1] < -2.0e9, "itof(min_i32) should be large negative")
	testing.expect_value(t, arr[2], 0.0)
	testing.expect_value(t, arr[3], 1.0)
}

// --- div/rem edge cases ---

@(test)
test_simd_div_f32_special :: proc(t: ^testing.T) {
	pos_inf := math.inf_f32(1)
	nan := math.nan_f32()
	a := vload(&(#simd[4]f32{1.0, pos_inf, 0.0, nan}))
	b := vload(&(#simd[4]f32{0.0, pos_inf, 0.0, 1.0}))
	result := intrinsics.simd_div(a, b)
	arr := transmute([4]f32)result
	testing.expect(t, math.is_inf(arr[0], 1), "1/0 should be +inf")
	testing.expect(t, math.is_nan(arr[1]), "inf/inf should be NaN")
	testing.expect(t, math.is_nan(arr[2]), "0/0 should be NaN")
	testing.expect(t, math.is_nan(arr[3]), "NaN/x should be NaN")
}

// --- bit_not with booleans ---
// NOTE: simd_bit_not on booleans does BITWISE complement, not logical NOT.
// Since Odin's `true` is 0x01 (not 0xFF), ~0x01 = 0xFE which is still truthy.
// For logical NOT on boolean vectors, use comparison against 0 or XOR with all-true.

@(test)
test_simd_bit_not_bool :: proc(t: ^testing.T) {
	// Verify that bit_not produces non-zero values for both true and false inputs
	// (since ~0x01=0xFE and ~0x00=0xFF are both non-zero)
	a := vload(&(#simd[4]bool{true, false, true, false}))
	result := intrinsics.simd_bit_not(a)
	// Check that all lanes are truthy (non-zero) after bitwise complement
	arr := transmute([4]u8)result
	for i in 0 ..< 4 {
		testing.expect(t, arr[i] != 0, "bit_not should produce non-zero for both true and false")
	}
}
