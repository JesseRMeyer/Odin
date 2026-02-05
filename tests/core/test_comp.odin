package test_comp

import "core:fmt"

// ===========================================================================
// Integer types — every fixed-width integer
// ===========================================================================

compute_i8 :: proc() -> i8   { return -42 }
compute_i16 :: proc() -> i16 { return -1234 }
compute_i32 :: proc() -> i32 { return -100_000 }
compute_i64 :: proc() -> i64 { return -9_000_000_000 }
compute_u8 :: proc() -> u8   { return 255 }
compute_u16 :: proc() -> u16 { return 65535 }
compute_u32 :: proc() -> u32 { return 4_000_000_000 }
compute_u64 :: proc() -> u64 { return 18_000_000_000_000_000_000 }

// ===========================================================================
// Boolean
// ===========================================================================

compute_true :: proc() -> bool  { return true }
compute_false :: proc() -> bool { return false }

// ===========================================================================
// Float types
// ===========================================================================

compute_f32 :: proc() -> f32 { return 3.14159265 }
compute_f64 :: proc() -> f64 {
	// Leibniz formula for pi
	result: f64 = 0.0
	for i: i32 = 0; i < 10000; i += 1 {
		sign: f64 = 1.0
		if i % 2 == 1 { sign = -1.0 }
		result += sign / f64(2 * i32(i) + 1)
	}
	return result * 4.0
}

// ===========================================================================
// Arithmetic and bitwise operations
// ===========================================================================

compute_bitwise :: proc() -> u32 {
	a: u32 = 0xDEAD_BEEF
	b: u32 = 0xCAFE_BABE
	return (a & b) | (a ~ b) // XOR and AND/OR
}

compute_shifts :: proc() -> u64 {
	val: u64 = 1
	// Build a bitmask: 1 | 2 | 4 | 8 | 16 | 32 | 64 | 128 = 255
	result: u64 = 0
	for i: u32 = 0; i < 8; i += 1 {
		result |= val << i
	}
	return result
}

compute_modular_arithmetic :: proc() -> i32 {
	// Compute 7^5 mod 1000 iteratively
	result: i32 = 1
	for i: i32 = 0; i < 5; i += 1 {
		result = (result * 7) % 1000
	}
	return result // 7^5 = 16807, mod 1000 = 807
}

// ===========================================================================
// Control flow — if/else, switch, for, nested loops
// ===========================================================================

compute_collatz_steps :: proc() -> i32 {
	// Collatz sequence for 27: famously takes 111 steps
	n: i32 = 27
	steps: i32 = 0
	for n != 1 {
		if n % 2 == 0 {
			n /= 2
		} else {
			n = 3 * n + 1
		}
		steps += 1
	}
	return steps
}

compute_switch :: proc() -> i32 {
	total: i32 = 0
	for i: i32 = 0; i < 10; i += 1 {
		switch i % 4 {
		case 0: total += 1
		case 1: total += 10
		case 2: total += 100
		case 3: total += 1000
		}
	}
	return total
	// i=0:1, i=1:10, i=2:100, i=3:1000, i=4:1, i=5:10, i=6:100, i=7:1000, i=8:1, i=9:10
	// = 3 + 30 + 200 + 2000 = 2233
}

// ===========================================================================
// Calling other pure functions — call chains
// ===========================================================================

helper_square :: proc(x: i32) -> i32 { return x * x }
helper_cube :: proc(x: i32) -> i32 { return x * helper_square(x) }
helper_sum_of_cubes :: proc(n: i32) -> i32 {
	total: i32 = 0
	for i: i32 = 1; i <= n; i += 1 {
		total += helper_cube(i)
	}
	return total
}

compute_sum_of_cubes :: proc() -> i32 {
	return helper_sum_of_cubes(10) // 1 + 8 + 27 + ... + 1000 = 3025
}

// ===========================================================================
// Recursion
// ===========================================================================

fib_recursive :: proc(n: i32) -> i32 {
	if n <= 1 { return n }
	return fib_recursive(n - 1) + fib_recursive(n - 2)
}

compute_fib_20 :: proc() -> i32 {
	return fib_recursive(20) // 6765
}

// ===========================================================================
// Ternary expressions
// ===========================================================================

abs_i32 :: proc(x: i32) -> i32 { return x >= 0 ? x : -x }

compute_ternary :: proc() -> i32 {
	return abs_i32(-42) + abs_i32(58) // 100
}

// ===========================================================================
// Type casts
// ===========================================================================

compute_casts :: proc() -> i32 {
	x: f64 = 3.7
	y: i32 = i32(x)       // truncation: 3
	z: f32 = f32(x)       // f64 -> f32
	w: i32 = i32(z) + y   // 3 + 3 = 6
	return w
}

compute_int_widening :: proc() -> i64 {
	a: i8 = 127
	b: i16 = i16(a) * 2   // 254
	c: i32 = i32(b) * 100 // 25400
	d: i64 = i64(c) * 1000 // 25400000
	return d
}

// ===========================================================================
// Enums — various backing types and operations
// ===========================================================================

Color :: enum u8 {
	Red   = 0,
	Green = 1,
	Blue  = 2,
}

compute_color :: proc() -> Color {
	return .Blue
}

Season :: enum i32 {
	Spring = 10,
	Summer = 20,
	Autumn = 30,
	Winter = 40,
}

compute_season :: proc() -> Season {
	// Pick season by "month"
	month: i32 = 7
	if month >= 3 && month < 6 { return .Spring }
	if month >= 6 && month < 9 { return .Summer }
	if month >= 9 && month < 12 { return .Autumn }
	return .Winter
}

// ===========================================================================
// Structs — simple, nested, with different field types
// ===========================================================================

Vec2 :: struct { x, y: f32 }

compute_vec2 :: proc() -> Vec2 {
	return Vec2{3.0, 4.0}
}

RGBA :: struct { r, g, b, a: u8 }

compute_rgba :: proc() -> RGBA {
	return RGBA{255, 128, 0, 255}
}

Rect :: struct {
	origin: Vec2,
	size:   Vec2,
}

compute_rect :: proc() -> Rect {
	return Rect{
		origin = Vec2{10.0, 20.0},
		size   = Vec2{100.0, 50.0},
	}
}

MixedStruct :: struct {
	flag:  bool,
	count: i32,
	value: f64,
	tag:   u8,
}

compute_mixed :: proc() -> MixedStruct {
	return MixedStruct{
		flag  = true,
		count = 42,
		value = 2.718281828,
		tag   = 0xAB,
	}
}

// Struct with computation
Transform2D :: struct {
	m00, m01, m10, m11: f32,
	tx, ty: f32,
}

compute_rotation_matrix :: proc() -> Transform2D {
	// Approximate 45-degree rotation
	// cos(45°) ≈ 0.7071, sin(45°) ≈ 0.7071
	c: f32 = 0.70710678
	s: f32 = 0.70710678
	return Transform2D{
		m00 = c, m01 = -s,
		m10 = s, m11 = c,
		tx = 0.0, ty = 0.0,
	}
}

// ===========================================================================
// Arrays — various element types and sizes
// ===========================================================================

compute_small_array :: proc() -> [4]i32 {
	return [4]i32{10, 20, 30, 40}
}

compute_byte_array :: proc() -> [8]u8 {
	result: [8]u8
	for i: u8 = 0; i < 8; i += 1 {
		result[i] = i * i
	}
	return result // {0, 1, 4, 9, 16, 25, 36, 49}
}

compute_bool_array :: proc() -> [8]bool {
	result: [8]bool
	for i: i32 = 0; i < 8; i += 1 {
		result[i] = i % 2 == 0 // true, false, true, false, ...
	}
	return result
}

// Array of structs
compute_triangle :: proc() -> [3]Vec2 {
	return [3]Vec2{
		Vec2{0.0, 0.0},
		Vec2{1.0, 0.0},
		Vec2{0.5, 0.866},
	}
}

// Larger array with computation
compute_primes_sieve :: proc() -> [50]bool {
	// Sieve of Eratosthenes for numbers 0..49
	is_prime: [50]bool
	for i: i32 = 2; i < 50; i += 1 {
		is_prime[i] = true
	}
	for i: i32 = 2; i * i < 50; i += 1 {
		if is_prime[i] {
			for j := i * i; j < 50; j += i {
				is_prime[j] = false
			}
		}
	}
	return is_prime
}

// 2D array (array of arrays)
compute_identity_3x3 :: proc() -> [3][3]f32 {
	result: [3][3]f32
	for i: i32 = 0; i < 3; i += 1 {
		for j: i32 = 0; j < 3; j += 1 {
			result[i][j] = i == j ? 1.0 : 0.0
		}
	}
	return result
}

// Array of enums
compute_color_cycle :: proc() -> [6]Color {
	return [6]Color{.Red, .Green, .Blue, .Red, .Green, .Blue}
}

// ===========================================================================
// Complex algorithms
// ===========================================================================

// Matrix multiply 3x3
Mat3 :: struct {
	e: [3][3]f32,
}

mat3_mul :: proc(a: Mat3, b: Mat3) -> Mat3 {
	result: Mat3
	for i: i32 = 0; i < 3; i += 1 {
		for j: i32 = 0; j < 3; j += 1 {
			sum: f32 = 0.0
			for k: i32 = 0; k < 3; k += 1 {
				sum += a.e[i][k] * b.e[k][j]
			}
			result.e[i][j] = sum
		}
	}
	return result
}

compute_mat3_product :: proc() -> Mat3 {
	a := Mat3{e = {
		{1.0, 2.0, 3.0},
		{4.0, 5.0, 6.0},
		{7.0, 8.0, 9.0},
	}}
	b := Mat3{e = {
		{9.0, 8.0, 7.0},
		{6.0, 5.0, 4.0},
		{3.0, 2.0, 1.0},
	}}
	return mat3_mul(a, b)
}

// Bubble sort
compute_sorted_array :: proc() -> [8]i32 {
	arr: [8]i32 = {64, 34, 25, 12, 22, 11, 90, 1}
	n: i32 = 8
	for i: i32 = 0; i < n - 1; i += 1 {
		for j: i32 = 0; j < n - i - 1; j += 1 {
			if arr[j] > arr[j + 1] {
				arr[j], arr[j + 1] = arr[j + 1], arr[j]
			}
		}
	}
	return arr
}

// GCD via Euclidean algorithm
gcd :: proc(a, b: i32) -> i32 {
	x := a
	y := b
	for y != 0 {
		x, y = y, x % y
	}
	return x
}

compute_gcd :: proc() -> i32 {
	return gcd(252, 105) // GCD = 21
}

// ===========================================================================
// Edge cases
// ===========================================================================

// Zero-value struct
compute_zero_struct :: proc() -> Vec2 {
	return Vec2{}
}

// Single-field struct
Wrapper :: struct { val: i32 }
compute_wrapper :: proc() -> Wrapper {
	return Wrapper{val = 99}
}

// Deeply nested control flow
compute_nested_loops :: proc() -> i32 {
	total: i32 = 0
	for i: i32 = 0; i < 5; i += 1 {
		for j: i32 = 0; j < 5; j += 1 {
			for k: i32 = 0; k < 5; k += 1 {
				if (i + j + k) % 3 == 0 {
					total += 1
				}
			}
		}
	}
	return total
}

// Large-ish computation to exercise the JIT
compute_hash :: proc() -> u32 {
	// FNV-1a hash of the string "Hello, #comp!"
	// We'll inline the bytes since we can't use string pointers
	bytes: [13]u8 = {'H', 'e', 'l', 'l', 'o', ',', ' ', '#', 'c', 'o', 'm', 'p', '!'}
	hash: u32 = 2166136261 // FNV offset basis
	for i: i32 = 0; i < 13; i += 1 {
		hash ~= u32(bytes[i])
		hash *= 16777619   // FNV prime
	}
	return hash
}

// Negative integer edge cases
compute_neg_edge :: proc() -> i32 {
	a: i32 = -2147483647 // min_i32 + 1
	b: i32 = a + 2147483646 // -1
	return b
}

// u8 wrapping
compute_u8_wrap :: proc() -> u8 {
	x: u8 = 200
	y: u8 = 100
	return x + y // wraps to 44 (300 - 256)
}

// Multiple levels of function calls
level_3 :: proc(x: i32) -> i32 { return x * 2 }
level_2 :: proc(x: i32) -> i32 { return level_3(x) + 1 }
level_1 :: proc(x: i32) -> i32 { return level_2(x) + level_2(x + 1) }
compute_deep_calls :: proc() -> i32 {
	return level_1(5) // level_2(5) + level_2(6) = (10+1) + (12+1) = 24
}

// ===========================================================================
// Struct with enum field
// ===========================================================================

Tagged :: struct {
	kind:  Color,
	value: i32,
}

compute_tagged :: proc() -> Tagged {
	return Tagged{kind = .Green, value = 123}
}

// Array of mixed structs
compute_tagged_array :: proc() -> [3]Tagged {
	return [3]Tagged{
		Tagged{kind = .Red, value = 1},
		Tagged{kind = .Green, value = 2},
		Tagged{kind = .Blue, value = 3},
	}
}

// ===========================================================================
// Named return value
// ===========================================================================

compute_named_return :: proc() -> (result: i32) {
	result = 0
	for i: i32 = 1; i <= 100; i += 1 {
		result += i
	}
	return
}

// ===========================================================================
// Struct returned by computation (not literal)
// ===========================================================================

compute_vec2_sum :: proc() -> Vec2 {
	a := Vec2{1.5, 2.5}
	b := Vec2{3.5, 4.5}
	return Vec2{a.x + b.x, a.y + b.y} // {5.0, 7.0}
}

// ===========================================================================
// i128 / u128
// ===========================================================================

compute_i128 :: proc() -> i128 {
	return i128(1_000_000_000) * i128(1_000_000_000) // 10^18
}

compute_u128 :: proc() -> u128 {
	return u128(max(u64)) + 1 // 2^64
}

// ===========================================================================
// Enum with explicit u8 backing
// ===========================================================================

Flags :: enum u8 {
	A = 1,
	B = 2,
	C = 4,
}

compute_flag :: proc() -> Flags {
	return .C
}

// ===========================================================================
// Array of f32
// ===========================================================================

compute_f32_array :: proc() -> [4]f32 {
	return [4]f32{1.0, 2.0, 3.0, 4.0}
}

// ===========================================================================
// Procedure parameters — passing compile-time constants to #comp
// ===========================================================================

// Basic integer parameter
double :: proc(x: i32) -> i32 {
	return x * 2
}

// Multiple parameters
add3 :: proc(a, b, c: i32) -> i32 {
	return a + b + c
}

// Float parameter
scale_f32 :: proc(x: f32, factor: f32) -> f32 {
	return x * factor
}

// Boolean parameter
choose :: proc(cond: bool, a, b: i32) -> i32 {
	if cond { return a }
	return b
}

// Struct parameter
vec2_add :: proc(a, b: Vec2) -> Vec2 {
	return Vec2{a.x + b.x, a.y + b.y}
}

// Array parameter
sum_array :: proc(arr: [4]i32) -> i32 {
	total: i32 = 0
	for i: i32 = 0; i < 4; i += 1 {
		total += arr[i]
	}
	return total
}

// Enum parameter
is_green :: proc(c: Color) -> bool {
	return c == .Green
}

// Mixed parameters
weighted_sum :: proc(weights: [3]f32, values: [3]i32) -> f32 {
	sum: f32 = 0.0
	for i: i32 = 0; i < 3; i += 1 {
		sum += weights[i] * f32(values[i])
	}
	return sum
}

// Recursive with parameter
factorial :: proc(n: i32) -> i32 {
	if n <= 1 { return 1 }
	return n * factorial(n - 1)
}

// Struct with computed fields parameter
transform_vec :: proc(v: Vec2, scale: f32, offset: f32) -> Vec2 {
	return Vec2{v.x * scale + offset, v.y * scale + offset}
}

// Nested struct parameter
mat_scale :: proc(m: Mat3, s: f32) -> Mat3 {
	result: Mat3
	for i: i32 = 0; i < 3; i += 1 {
		for j: i32 = 0; j < 3; j += 1 {
			result.e[i][j] = m.e[i][j] * s
		}
	}
	return result
}

// Enum with backing type parameter
flag_value :: proc(f: Flags) -> u8 {
	return u8(f)
}

// Chained #comp — one #comp feeds another
compute_base :: proc() -> i32 {
	return 5
}

multiply :: proc(x: i32, factor: i32) -> i32 {
	return x * factor
}

// ===========================================================================
// Constant binding and package scope
// ===========================================================================

// #comp at package scope — result is Addressing_Constant, usable in :: decl
PKG_CONST :: #comp compute_i32()
PKG_DOUBLED :: #comp double(21)

// ===========================================================================
// Distinct types
// ===========================================================================

Meters :: distinct f32

compute_meters :: proc() -> Meters {
	return Meters(42.5)
}

add_meters :: proc(a, b: Meters) -> Meters {
	return Meters(f32(a) + f32(b))
}

// ===========================================================================
// Wider parameter types (exercise different ABI paths)
// ===========================================================================

double_i8  :: proc(x: i8) -> i8   { return x * 2 }
double_i64 :: proc(x: i64) -> i64 { return x * 2 }
double_u64 :: proc(x: u64) -> u64 { return x * 2 }
scale_f64  :: proc(x: f64, s: f64) -> f64 { return x * s }
add_i128   :: proc(a, b: i128) -> i128 { return a + b }

// ===========================================================================
// Mutual recursion
// ===========================================================================

is_even_comp :: proc(n: i32) -> bool {
	if n == 0 { return true }
	return is_odd_comp(n - 1)
}

is_odd_comp :: proc(n: i32) -> bool {
	if n == 0 { return false }
	return is_even_comp(n - 1)
}

// ===========================================================================
// Main — run all tests
// ===========================================================================

expect :: proc(name: string, ok: bool) {
	if !ok {
		fmt.printf("FAIL: %s\n", name)
		panic("test failed")
	}
}

f32_near :: proc(a, b: f32, eps: f32 = 0.001) -> bool {
	d := a - b
	return d > -eps && d < eps
}

f64_near :: proc(a, b: f64, eps: f64 = 0.0001) -> bool {
	d := a - b
	return d > -eps && d < eps
}

main :: proc() {
	passed := 0
	total  := 0

	// --- Integer types ---
	{
		total += 8
		v_i8  := #comp compute_i8()
		v_i16 := #comp compute_i16()
		v_i32 := #comp compute_i32()
		v_i64 := #comp compute_i64()
		v_u8  := #comp compute_u8()
		v_u16 := #comp compute_u16()
		v_u32 := #comp compute_u32()
		v_u64 := #comp compute_u64()

		expect("i8",  v_i8  == -42);               passed += 1
		expect("i16", v_i16 == -1234);              passed += 1
		expect("i32", v_i32 == -100_000);           passed += 1
		expect("i64", v_i64 == -9_000_000_000);     passed += 1
		expect("u8",  v_u8  == 255);                passed += 1
		expect("u16", v_u16 == 65535);               passed += 1
		expect("u32", v_u32 == 4_000_000_000);       passed += 1
		expect("u64", v_u64 == 18_000_000_000_000_000_000); passed += 1
		fmt.println("  integers: OK")
	}

	// --- Booleans ---
	{
		total += 2
		vt := #comp compute_true()
		vf := #comp compute_false()
		expect("bool_true",  vt == true);  passed += 1
		expect("bool_false", vf == false); passed += 1
		fmt.println("  booleans: OK")
	}

	// --- Floats ---
	{
		total += 2
		v32 := #comp compute_f32()
		v64 := #comp compute_f64()
		expect("f32_pi", f32_near(v32, 3.14159265)); passed += 1
		expect("f64_pi", f64_near(v64, 3.14159265, 0.001)); passed += 1
		fmt.println("  floats: OK")
	}

	// --- Bitwise ---
	{
		total += 2
		vb := #comp compute_bitwise()
		vs := #comp compute_shifts()
		expect("bitwise", vb == (0xDEAD_BEEF & 0xCAFE_BABE) | (0xDEAD_BEEF ~ 0xCAFE_BABE)); passed += 1
		expect("shifts", vs == 255); passed += 1
		fmt.println("  bitwise: OK")
	}

	// --- Modular arithmetic ---
	{
		total += 1
		vm := #comp compute_modular_arithmetic()
		expect("mod_pow", vm == 807); passed += 1
		fmt.println("  mod arithmetic: OK")
	}

	// --- Control flow ---
	{
		total += 2
		vc := #comp compute_collatz_steps()
		vsw := #comp compute_switch()
		expect("collatz_27", vc == 111); passed += 1
		expect("switch", vsw == 2233); passed += 1
		fmt.println("  control flow: OK")
	}

	// --- Call chains ---
	{
		total += 1
		vsc := #comp compute_sum_of_cubes()
		expect("sum_of_cubes", vsc == 3025); passed += 1
		fmt.println("  call chains: OK")
	}

	// --- Recursion ---
	{
		total += 1
		vfib := #comp compute_fib_20()
		expect("fib_20", vfib == 6765); passed += 1
		fmt.println("  recursion: OK")
	}

	// --- Ternary ---
	{
		total += 1
		vt := #comp compute_ternary()
		expect("ternary_abs", vt == 100); passed += 1
		fmt.println("  ternary: OK")
	}

	// --- Type casts ---
	{
		total += 2
		vc := #comp compute_casts()
		vw := #comp compute_int_widening()
		expect("casts", vc == 6); passed += 1
		expect("int_widening", vw == 25400000); passed += 1
		fmt.println("  type casts: OK")
	}

	// --- Enums ---
	{
		total += 2
		vcolor := #comp compute_color()
		vseason := #comp compute_season()
		expect("color", vcolor == .Blue); passed += 1
		expect("season", vseason == .Summer); passed += 1
		fmt.println("  enums: OK")
	}

	// --- Structs ---
	{
		total += 5
		v2 := #comp compute_vec2()
		expect("vec2_x", f32_near(v2.x, 3.0)); passed += 1
		expect("vec2_y", f32_near(v2.y, 4.0)); passed += 1

		rgba := #comp compute_rgba()
		expect("rgba", rgba.r == 255 && rgba.g == 128 && rgba.b == 0 && rgba.a == 255); passed += 1

		rect := #comp compute_rect()
		expect("rect", f32_near(rect.origin.x, 10.0) && f32_near(rect.origin.y, 20.0) &&
		               f32_near(rect.size.x, 100.0) && f32_near(rect.size.y, 50.0)); passed += 1

		mixed := #comp compute_mixed()
		expect("mixed", mixed.flag == true && mixed.count == 42 &&
		                f64_near(mixed.value, 2.718281828) && mixed.tag == 0xAB); passed += 1
		fmt.println("  structs: OK")
	}

	// --- Nested struct ---
	{
		total += 1
		rot := #comp compute_rotation_matrix()
		expect("rotation", f32_near(rot.m00, 0.7071) && f32_near(rot.m01, -0.7071) &&
		                   f32_near(rot.m10, 0.7071) && f32_near(rot.m11, 0.7071) &&
		                   f32_near(rot.tx, 0.0) && f32_near(rot.ty, 0.0)); passed += 1
		fmt.println("  nested struct: OK")
	}

	// --- Arrays ---
	{
		total += 5
		small := #comp compute_small_array()
		expect("small_arr", small[0] == 10 && small[1] == 20 && small[2] == 30 && small[3] == 40); passed += 1

		bytes := #comp compute_byte_array()
		expect("byte_arr", bytes[0] == 0 && bytes[1] == 1 && bytes[4] == 16 && bytes[7] == 49); passed += 1

		bools := #comp compute_bool_array()
		expect("bool_arr", bools[0] == true && bools[1] == false && bools[6] == true && bools[7] == false); passed += 1

		tri := #comp compute_triangle()
		expect("triangle", f32_near(tri[0].x, 0.0) && f32_near(tri[1].x, 1.0) &&
		                   f32_near(tri[2].y, 0.866)); passed += 1

		colors := #comp compute_color_cycle()
		expect("color_cycle", colors[0] == .Red && colors[1] == .Green && colors[2] == .Blue &&
		                      colors[3] == .Red && colors[4] == .Green && colors[5] == .Blue); passed += 1
		fmt.println("  arrays: OK")
	}

	// --- Sieve ---
	{
		total += 1
		sieve := #comp compute_primes_sieve()
		// Primes under 50: 2,3,5,7,11,13,17,19,23,29,31,37,41,43,47
		expect("sieve", sieve[2] && sieve[3] && sieve[5] && sieve[7] && sieve[11] &&
		                sieve[13] && sieve[17] && sieve[19] && sieve[23] && sieve[29] &&
		                sieve[31] && sieve[37] && sieve[41] && sieve[43] && sieve[47] &&
		                !sieve[0] && !sieve[1] && !sieve[4] && !sieve[6] && !sieve[9] &&
		                !sieve[15] && !sieve[25] && !sieve[49]); passed += 1
		fmt.println("  prime sieve: OK")
	}

	// --- 2D array (identity matrix) ---
	{
		total += 1
		ident := #comp compute_identity_3x3()
		ok := true
		for i: i32 = 0; i < 3; i += 1 {
			for j: i32 = 0; j < 3; j += 1 {
				expected: f32 = i == j ? 1.0 : 0.0
				if !f32_near(ident[i][j], expected) { ok = false }
			}
		}
		expect("identity_3x3", ok); passed += 1
		fmt.println("  2D array: OK")
	}

	// --- Matrix multiply ---
	{
		total += 1
		prod := #comp compute_mat3_product()
		// Row 0: 1*9+2*6+3*3=30, 1*8+2*5+3*2=24, 1*7+2*4+3*1=18
		// Row 1: 4*9+5*6+6*3=84, 4*8+5*5+6*2=69, 4*7+5*4+6*1=54
		// Row 2: 7*9+8*6+9*3=138, 7*8+8*5+9*2=114, 7*7+8*4+9*1=90
		expect("mat3_mul",
			f32_near(prod.e[0][0], 30.0) && f32_near(prod.e[0][1], 24.0) && f32_near(prod.e[0][2], 18.0) &&
			f32_near(prod.e[1][0], 84.0) && f32_near(prod.e[1][1], 69.0) && f32_near(prod.e[1][2], 54.0) &&
			f32_near(prod.e[2][0], 138.0) && f32_near(prod.e[2][1], 114.0) && f32_near(prod.e[2][2], 90.0)); passed += 1
		fmt.println("  matrix multiply: OK")
	}

	// --- Bubble sort ---
	{
		total += 1
		sorted := #comp compute_sorted_array()
		expect("sorted", sorted[0] == 1 && sorted[1] == 11 && sorted[2] == 12 &&
		                 sorted[3] == 22 && sorted[4] == 25 && sorted[5] == 34 &&
		                 sorted[6] == 64 && sorted[7] == 90); passed += 1
		fmt.println("  bubble sort: OK")
	}

	// --- GCD ---
	{
		total += 1
		vgcd := #comp compute_gcd()
		expect("gcd", vgcd == 21); passed += 1
		fmt.println("  GCD: OK")
	}

	// --- Edge cases ---
	{
		total += 5
		zero := #comp compute_zero_struct()
		expect("zero_struct", f32_near(zero.x, 0.0) && f32_near(zero.y, 0.0)); passed += 1

		wrap := #comp compute_wrapper()
		expect("wrapper", wrap.val == 99); passed += 1

		nested := #comp compute_nested_loops()
		expect("nested_loops", nested == 41); passed += 1

		hash := #comp compute_hash()
		// Compute expected FNV-1a hash manually
		expected_hash: u32 = 2166136261
		hello_bytes: [13]u8 = {'H', 'e', 'l', 'l', 'o', ',', ' ', '#', 'c', 'o', 'm', 'p', '!'}
		for i: i32 = 0; i < 13; i += 1 {
			expected_hash ~= u32(hello_bytes[i])
			expected_hash *= 16777619
		}
		expect("fnv1a_hash", hash == expected_hash); passed += 1

		neg := #comp compute_neg_edge()
		expect("neg_edge", neg == -1); passed += 1
		fmt.println("  edge cases: OK")
	}

	// --- u8 wrapping ---
	{
		total += 1
		vw := #comp compute_u8_wrap()
		expect("u8_wrap", vw == 44); passed += 1
		fmt.println("  u8 wrapping: OK")
	}

	// --- Deep call chain ---
	{
		total += 1
		vdc := #comp compute_deep_calls()
		expect("deep_calls", vdc == 24); passed += 1
		fmt.println("  deep calls: OK")
	}

	// --- Struct with enum ---
	{
		total += 2
		tagged := #comp compute_tagged()
		expect("tagged", tagged.kind == .Green && tagged.value == 123); passed += 1

		tarr := #comp compute_tagged_array()
		expect("tagged_arr", tarr[0].kind == .Red && tarr[0].value == 1 &&
		                     tarr[1].kind == .Green && tarr[1].value == 2 &&
		                     tarr[2].kind == .Blue && tarr[2].value == 3); passed += 1
		fmt.println("  struct+enum: OK")
	}

	// --- Named return value ---
	{
		total += 1
		nr := #comp compute_named_return()
		expect("named_return", nr == 5050); passed += 1
		fmt.println("  named return: OK")
	}

	// --- Struct from computation ---
	{
		total += 1
		vs := #comp compute_vec2_sum()
		expect("vec2_sum", f32_near(vs.x, 5.0) && f32_near(vs.y, 7.0)); passed += 1
		fmt.println("  struct computation: OK")
	}

	// --- i128/u128 ---
	{
		total += 2
		vi := #comp compute_i128()
		expect("i128", vi == i128(1_000_000_000) * i128(1_000_000_000)); passed += 1

		vu := #comp compute_u128()
		expect("u128", vu == u128(max(u64)) + 1); passed += 1
		fmt.println("  128-bit integers: OK")
	}

	// --- Enum with u8 backing ---
	{
		total += 1
		vf := #comp compute_flag()
		expect("flag_enum", vf == .C); passed += 1
		fmt.println("  u8 enum: OK")
	}

	// --- f32 array ---
	{
		total += 1
		fa := #comp compute_f32_array()
		expect("f32_array", f32_near(fa[0], 1.0) && f32_near(fa[1], 2.0) &&
		                    f32_near(fa[2], 3.0) && f32_near(fa[3], 4.0)); passed += 1
		fmt.println("  f32 array: OK")
	}

	// --- Procedure parameters ---
	{
		total += 14

		// Basic integer parameter
		d := #comp double(21)
		expect("param_double", d == 42); passed += 1

		// Multiple parameters
		s := #comp add3(10, 20, 30)
		expect("param_add3", s == 60); passed += 1

		// Float parameters
		sf := #comp scale_f32(2.5, 4.0)
		expect("param_scale_f32", f32_near(sf, 10.0)); passed += 1

		// Boolean parameter
		c1 := #comp choose(true, 100, 200)
		c2 := #comp choose(false, 100, 200)
		expect("param_choose", c1 == 100 && c2 == 200); passed += 1

		// Struct parameter
		V1 :: Vec2{1.0, 2.0}
		V2 :: Vec2{3.0, 4.0}
		vs := #comp vec2_add(V1, V2)
		expect("param_vec2_add", f32_near(vs.x, 4.0) && f32_near(vs.y, 6.0)); passed += 1

		// Array parameter
		ARR :: [4]i32{1, 2, 3, 4}
		arr_sum := #comp sum_array(ARR)
		expect("param_sum_array", arr_sum == 10); passed += 1

		// Enum parameter
		g := #comp is_green(.Green)
		ng := #comp is_green(.Red)
		expect("param_enum", g == true && ng == false); passed += 1

		// Mixed array parameters
		WEIGHTS :: [3]f32{1.0, 2.0, 3.0}
		VALUES  :: [3]i32{10, 20, 30}
		ws := #comp weighted_sum(WEIGHTS, VALUES)
		// 1*10 + 2*20 + 3*30 = 10 + 40 + 90 = 140
		expect("param_mixed", f32_near(ws, 140.0)); passed += 1

		// Recursive with parameter
		f5 := #comp factorial(5)
		expect("param_factorial", f5 == 120); passed += 1

		// Struct with multiple params
		V3 :: Vec2{2.0, 3.0}
		tv := #comp transform_vec(V3, 2.0, 1.0)
		expect("param_transform", f32_near(tv.x, 5.0) && f32_near(tv.y, 7.0)); passed += 1

		// Nested struct parameter
		M :: Mat3{e = {{1.0, 2.0, 3.0}, {4.0, 5.0, 6.0}, {7.0, 8.0, 9.0}}}
		ms := #comp mat_scale(M, 2.0)
		expect("param_mat_scale", f32_near(ms.e[0][0], 2.0) && f32_near(ms.e[1][1], 10.0) && f32_near(ms.e[2][2], 18.0)); passed += 1

		// Enum with backing type
		fv := #comp flag_value(.C)
		expect("param_flag", fv == 4); passed += 1

		// Chained #comp
		chained := #comp multiply(#comp compute_base(), 10)
		expect("param_chained", chained == 50); passed += 1

		// Constant expression as argument
		N :: 7
		expr_arg := #comp double(N + 3)
		expect("param_const_expr", expr_arg == 20); passed += 1

		fmt.println("  procedure parameters: OK")
	}

	// --- Constant binding and package scope ---
	{
		total += 3
		expect("pkg_const", PKG_CONST == -100_000); passed += 1
		expect("pkg_doubled", PKG_DOUBLED == 42); passed += 1

		// Multiple #comp in a single expression
		multi := #comp double(10) + #comp double(20)
		expect("multi_comp", multi == 60); passed += 1
		fmt.println("  constant binding: OK")
	}

	// --- Distinct types ---
	{
		total += 2
		m := #comp compute_meters()
		expect("distinct_return", f32_near(f32(m), 42.5)); passed += 1

		M1 :: Meters(10.0)
		M2 :: Meters(20.0)
		ms := #comp add_meters(M1, M2)
		expect("distinct_param", f32_near(f32(ms), 30.0)); passed += 1
		fmt.println("  distinct types: OK")
	}

	// --- Wider parameter types ---
	{
		total += 5
		vi8 := #comp double_i8(21)
		expect("param_i8", vi8 == 42); passed += 1

		vi64 := #comp double_i64(1_000_000_000)
		expect("param_i64", vi64 == 2_000_000_000); passed += 1

		vu64 := #comp double_u64(9_000_000_000)
		expect("param_u64", vu64 == 18_000_000_000); passed += 1

		vf64 := #comp scale_f64(2.5, 4.0)
		expect("param_f64", f64_near(vf64, 10.0)); passed += 1

		v128 := #comp add_i128(i128(1_000_000_000_000), i128(2_000_000_000_000))
		expect("param_i128", v128 == i128(3_000_000_000_000)); passed += 1
		fmt.println("  wider params: OK")
	}

	// --- Mutual recursion ---
	{
		total += 2
		ve := #comp is_even_comp(10)
		expect("mutual_even", ve == true); passed += 1

		vo := #comp is_odd_comp(7)
		expect("mutual_odd", vo == true); passed += 1
		fmt.println("  mutual recursion: OK")
	}

	// --- Summary ---
	fmt.printf("\n%d / %d tests passed\n", passed, total)
	if passed == total {
		fmt.println("All #comp tests passed!")
	} else {
		fmt.printf("FAILED: %d tests did not pass\n", total - passed)
		panic("test suite failed")
	}
}
