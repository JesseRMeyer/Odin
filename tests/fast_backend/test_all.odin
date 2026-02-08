package test_all

// Unified fast backend test suite.
// Single file, single build, single run.
// Exit code indicates which check failed (0 = all pass).
//
// Exit code ranges:
//   100-109  branch spill / basic control flow
//   110-169  control flow (branches, loops, calls)
//   200-211  multi-return
//   300-353  floats, ranges, boolean logic
//   400-450  stress (fibonacci, GCD, classify, nesting, search, complex loops)
//   500-520  strings
//   600-612  switch (basic)
//   700-740  switch (advanced)
//   800-850  slicing
//   900-905  or_else
//   950-969  globals
//   1000-1031 ternary if/when, implicit selectors, selector calls
//   1100-1127 type switch, struct type assertions, labeled break regression
//   1200-1241 any boxing, selector expressions
//   1300-1341 signed narrow types
//   1400-1452 signed ordering comparisons
//   1500-1541 any type switch
//   1600-1649 string comparison
//   1700-1730 procedure values and indirect calls

foreign import libc "system:c"
foreign libc {
	exit  :: proc "c" (code: i32) ---
	write :: proc "c" (fd: i32, buf: rawptr, count: uint) -> int ---
}

print_msg :: proc(msg: string) {
	write(1, raw_data(msg), cast(uint)len(msg))
}

check :: proc(cond: bool, code: i32) {
	if !cond {
		exit(code)
	}
}

// ═══════════════════════════════════════════════════════════════════════
// Branch spill / basic control flow (100-109)
// ═══════════════════════════════════════════════════════════════════════

test_branch_spill :: proc() {
	a : int = 3 + 4
	check(a == 7, 100)
	b : int = a * 2
	check(b == 14, 101)
}

// ═══════════════════════════════════════════════════════════════════════
// Control flow (110-169)
// ═══════════════════════════════════════════════════════════════════════

add :: proc(a: int, b: int) -> int { return a + b }
mul :: proc(a: int, b: int) -> int { return a * b }

test_multi_branch :: proc() {
	a := 10
	b := 20
	c := a + b
	check(c == 30, 110)
	d := c * 2
	check(d == 60, 111)
	e := d - a
	check(e == 50, 112)
	f := e / 5
	check(f == 10, 113)
}

test_nested_if :: proc() {
	x := 42
	if x > 0 {
		if x > 100 {
			exit(120)
		} else {
			check(x == 42, 121)
		}
	} else {
		exit(122)
	}
}

test_for_loop :: proc() {
	sum := 0
	for i := 0; i < 10; i += 1 {
		sum += i
	}
	check(sum == 45, 130)
}

test_nested_loop :: proc() {
	total := 0
	for i := 0; i < 5; i += 1 {
		for j := 0; j < 3; j += 1 {
			total += 1
		}
	}
	check(total == 15, 140)
}

test_call_across_branch :: proc() {
	a := add(3, 4)
	check(a == 7, 150)
	b := mul(a, 3)
	check(b == 21, 151)
	c := add(b, a)
	check(c == 28, 152)
}

test_break_continue :: proc() {
	sum := 0
	for i := 0; i < 20; i += 1 {
		if i == 10 { break }
		if i % 2 == 0 { continue }
		sum += i
	}
	check(sum == 25, 160) // odd 1..9: 1+3+5+7+9
}

test_early_return :: proc() -> int {
	for i := 0; i < 100; i += 1 {
		if i == 7 { return i }
	}
	return -1
}

// ═══════════════════════════════════════════════════════════════════════
// Multi-return (200-211)
// ═══════════════════════════════════════════════════════════════════════

two_vals :: proc() -> (int, bool) { return 42, true }
three_vals :: proc() -> (int, int, bool) { return 10, 20, true }
swap :: proc(a: int, b: int) -> (int, int) { return b, a }

test_multi_return :: proc() {
	a, ok := two_vals()
	check(a == 42, 200)
	check(ok, 201)

	x, y, ok2 := three_vals()
	check(x == 10, 202)
	check(y == 20, 203)
	check(ok2, 204)

	p, q := swap(100, 200)
	check(p == 200, 205)
	check(q == 100, 206)

	a, ok = two_vals()
	check(a == 42, 207)
	check(ok, 208)

	_, ok3 := two_vals()
	check(ok3, 209)

	v, _ := swap(5, 6)
	check(v == 6, 210)
}

// ═══════════════════════════════════════════════════════════════════════
// Floats, ranges, boolean logic (300-353)
// ═══════════════════════════════════════════════════════════════════════

test_float :: proc() {
	a : f64 = 3.5
	b : f64 = 2.0
	check(a + b == 5.5, 300)
	check(a * b == 7.0, 301)
	check(a - b == 1.5, 302)
	check(a / b == 1.75, 303)
}

test_range_int :: proc() {
	sum := 0
	for i in 0..<5 { sum += i }
	check(sum == 10, 310)
}

test_range_array :: proc() {
	arr := [4]int{10, 20, 30, 40}
	sum := 0
	for val in arr { sum += val }
	check(sum == 100, 320)
}

test_range_index :: proc() {
	arr := [3]int{100, 200, 300}
	idx_sum := 0
	val_sum := 0
	for val, idx in arr {
		idx_sum += idx
		val_sum += val
	}
	check(idx_sum == 3, 330)
	check(val_sum == 600, 331)
}

test_nested_range :: proc() {
	total := 0
	for i in 0..<3 {
		for j in 0..<4 { total += 1 }
	}
	check(total == 12, 340)
}

test_bool_logic :: proc() {
	a := true
	b := false
	check(a && !b, 350)
	check(a || b, 351)
	check(!(a && b), 352)
	c := 5
	check(c > 3 && c < 10, 353)
}

// ═══════════════════════════════════════════════════════════════════════
// Stress: fibonacci, GCD, classify, nesting, search, complex loops (400-450)
// ═══════════════════════════════════════════════════════════════════════

fib :: proc(n: int) -> int {
	if n <= 1 { return n }
	a, b := 0, 1
	for i := 2; i <= n; i += 1 {
		c := a + b
		a = b
		b = c
	}
	return b
}

gcd :: proc(a: int, b: int) -> int {
	x, y := a, b
	for y != 0 {
		t := y
		y = x % y
		x = t
	}
	return x
}

classify :: proc(x: int) -> int {
	if x < 0       { return -1 }
	else if x == 0  { return 0 }
	else if x < 10  { return 1 }
	else if x < 100 { return 2 }
	else            { return 3 }
}

deep_nest :: proc(a: int, b: int, c: int) -> int {
	result := 0
	if a > 0 {
		if b > 0 {
			if c > 0 { result = a + b + c }
			else     { result = a + b }
		} else {
			if c > 0 { result = a + c }
			else     { result = a }
		}
	}
	return result
}

find_first :: proc(target: int) -> int {
	data := [8]int{5, 12, 3, 7, 15, 1, 9, 11}
	for val, idx in data {
		if val == target { return idx }
	}
	return -1
}

complex_loop :: proc(n: int) -> int {
	sum := 0
	prod := 1
	for i := 1; i <= n; i += 1 {
		if i % 3 == 0 {
			sum += i * 2
		} else if i % 2 == 0 {
			sum += i
		} else {
			prod *= i
			if prod > 1000 { prod = 1 }
		}
	}
	return sum + prod
}

test_stress :: proc() {
	check(fib(0) == 0, 400)
	check(fib(1) == 1, 401)
	check(fib(10) == 55, 402)
	check(fib(20) == 6765, 403)

	check(gcd(12, 8) == 4, 410)
	check(gcd(100, 75) == 25, 411)
	check(gcd(17, 13) == 1, 412)
	check(gcd(0, 5) == 5, 413)

	check(classify(-5) == -1, 420)
	check(classify(0) == 0, 421)
	check(classify(7) == 1, 422)
	check(classify(50) == 2, 423)
	check(classify(200) == 3, 424)

	check(deep_nest(1, 1, 1) == 3, 430)
	check(deep_nest(1, 1, 0) == 2, 431)
	check(deep_nest(1, 0, 1) == 2, 432)
	check(deep_nest(1, 0, 0) == 1, 433)
	check(deep_nest(0, 1, 1) == 0, 434)

	check(find_first(7) == 3, 440)
	check(find_first(5) == 0, 441)
	check(find_first(11) == 7, 442)
	check(find_first(99) == -1, 443)

	check(complex_loop(15) == 129, 450)
}

// ═══════════════════════════════════════════════════════════════════════
// Strings (500-520)
// ═══════════════════════════════════════════════════════════════════════

str_len :: proc(s: string) -> int { return len(s) }

test_strings :: proc() {
	s := "hello"
	check(len(s) == 5, 500)
	empty := ""
	check(len(empty) == 0, 501)
	longer := "hello, world!"
	check(len(longer) == 13, 502)

	// Comparison (interned: same length)
	a := "abc"
	b := "abc"
	check(len(a) == len(b), 503)
	check(len(a) == 3, 504)

	// Passing to function
	check(str_len("test") == 4, 505)

	// Indexing
	check(s[0] == 'h', 510)
	check(s[4] == 'o', 511)
}

// ═══════════════════════════════════════════════════════════════════════
// Switch — basic (600-612)
// ═══════════════════════════════════════════════════════════════════════

test_switch_basic :: proc() {
	// Constant cases
	x := 2
	result := 0
	switch x {
	case 1: result = 10
	case 2: result = 20
	case 3: result = 30
	}
	check(result == 20, 600)

	// Default
	result = 0
	switch 99 {
	case 1: result = 10
	case 2: result = 20
	case:   result = -1
	}
	check(result == -1, 601)

	// Multi-value
	result = 0
	switch 3 {
	case 1, 2, 3: result = 100
	case 4, 5:    result = 200
	case:         result = 300
	}
	check(result == 100, 602)

	// Tag-less boolean switch
	v := 42
	result = 0
	switch {
	case v < 10:  result = 1
	case v < 50:  result = 2
	case v < 100: result = 3
	case:         result = 4
	}
	check(result == 2, 603)
}

switch_classify :: proc(x: int) -> int {
	switch {
	case x < 0:  return -1
	case x == 0: return 0
	case:        return 1
	}
}

test_switch_features :: proc() {
	// Fallthrough
	x := 1
	result := 0
	switch x {
	case 1:
		result += 10
		fallthrough
	case 2:
		result += 20
	case 3:
		result += 30
	}
	check(result == 30, 604)

	// Init statement
	result = 0
	switch y := 5; y {
	case 5: result = 50
	case:   result = -1
	}
	check(result == 50, 605)

	// Nested switch
	result = 0
	switch 1 {
	case 1:
		switch 2 {
		case 1: result = 11
		case 2: result = 12
		}
	case 2:
		result = 20
	}
	check(result == 12, 606)

	// Switch in a loop
	sum := 0
	for i := 0; i < 5; i += 1 {
		switch i {
		case 0: sum += 1
		case 1: sum += 10
		case 2: sum += 100
		case:   sum += 1000
		}
	}
	check(sum == 2111, 607)

	// Return from switch
	check(switch_classify(-5) == -1, 610)
	check(switch_classify(0) == 0, 611)
	check(switch_classify(7) == 1, 612)
}

// ═══════════════════════════════════════════════════════════════════════
// Switch — advanced (700-740)
// ═══════════════════════════════════════════════════════════════════════

grade :: proc(score: int) -> int {
	switch {
	case score >= 90: return 4
	case score >= 80: return 3
	case score >= 70: return 2
	case score >= 60: return 1
	case:             return 0
	}
}

test_switch_advanced :: proc() {
	// Range-style (boolean switch)
	check(grade(95) == 4, 700)
	check(grade(85) == 3, 701)
	check(grade(75) == 2, 702)
	check(grade(65) == 1, 703)
	check(grade(50) == 0, 704)

	// No match, no default
	x := 42
	result := -1
	switch x {
	case 1: result = 1
	case 2: result = 2
	}
	check(result == -1, 710)

	// Single case
	result = 0
	switch 5 {
	case 5: result = 50
	}
	check(result == 50, 715)

	// Fallthrough chain
	result = 0
	switch 1 {
	case 1:
		result += 1
		fallthrough
	case 2:
		result += 10
		fallthrough
	case 3:
		result += 100
	}
	check(result == 111, 720)

	// Bool switch
	b := true
	result = 0
	switch b {
	case true:  result = 1
	case false: result = 2
	}
	check(result == 1, 725)

	b = false
	result = 0
	switch b {
	case true:  result = 1
	case false: result = 2
	}
	check(result == 2, 726)

	// Switch-in-switch-in-loop
	total := 0
	for i := 0; i < 3; i += 1 {
		switch i {
		case 0:
			for j := 0; j < 3; j += 1 {
				switch j {
				case 0: total += 1
				case 1: total += 2
				case 2: total += 4
				}
			}
		case 1: total += 100
		case 2: total += 1000
		}
	}
	check(total == 1107, 730)

	// Default in middle
	result = 0
	switch 99 {
	case 1: result = 1
	case:   result = -1
	case 2: result = 2
	}
	check(result == -1, 735)

	// Empty case body
	result = 10
	switch 2 {
	case 1: result = 1
	case 2: // empty
	case 3: result = 3
	}
	check(result == 10, 740)
}

// ═══════════════════════════════════════════════════════════════════════
// Slicing (800-850)
// ═══════════════════════════════════════════════════════════════════════

sum_slice :: proc(s: []int) -> int {
	total := 0
	for i := 0; i < len(s); i += 1 { total += s[i] }
	return total
}

test_slicing :: proc() {
	arr := [5]int{10, 20, 30, 40, 50}

	// Basic
	s := arr[1:4]
	check(len(s) == 3, 800)
	check(s[0] == 20, 801)
	check(s[1] == 30, 802)
	check(s[2] == 40, 803)

	// Full slice
	s2 := arr[:]
	check(len(s2) == 5, 805)
	check(s2[0] == 10, 806)
	check(s2[4] == 50, 807)

	// Low only
	s3 := arr[3:]
	check(len(s3) == 2, 810)
	check(s3[0] == 40, 811)

	// High only
	s4 := arr[:2]
	check(len(s4) == 2, 815)
	check(s4[1] == 20, 816)

	// Slice of slice
	arr6 := [6]int{1, 2, 3, 4, 5, 6}
	s5 := arr6[1:5]
	s6 := s5[1:3]
	check(len(s6) == 2, 820)
	check(s6[0] == 3, 821)
	check(s6[1] == 4, 822)

	// String slicing
	str := "hello, world"
	sub := str[7:]
	check(len(sub) == 5, 825)
	check(sub[0] == 'w', 826)
	sub2 := str[:5]
	check(len(sub2) == 5, 830)
	check(sub2[0] == 'h', 831)

	// Empty slice
	s7 := arr[1:1]
	check(len(s7) == 0, 835)

	// Pass slice to function
	s8 := arr[1:3]
	check(sum_slice(s8) == 50, 840)

	// Slice in loop
	total := 0
	for i := 0; i < 4; i += 1 {
		s9 := arr[i:i+2]
		total += s9[0] + s9[1]
	}
	// (10+20)+(20+30)+(30+40)+(40+50) = 30+50+70+90 = 240
	check(total == 240, 845)
}

// ═══════════════════════════════════════════════════════════════════════
// or_else (900-905)
// ═══════════════════════════════════════════════════════════════════════

try_get :: proc(ok: bool, val: int) -> (int, bool) { return val, ok }
or_fallback :: proc() -> int { return 777 }

test_or_else :: proc() {
	check((try_get(true, 42) or_else 99) == 42, 900)
	check((try_get(false, 0) or_else 99) == 99, 901)

	// In a loop
	sum := 0
	for i := 0; i < 5; i += 1 {
		sum += try_get(i < 3, i * 10) or_else -1
	}
	check(sum == 28, 902) // 0+10+20+(-1)+(-1)

	// Call fallback
	check((try_get(false, 0) or_else or_fallback()) == 777, 903)

	// Chained
	x := try_get(false, 0) or_else 100
	y := try_get(true, x) or_else 200
	check(y == 100, 904)
}

// ═══════════════════════════════════════════════════════════════════════
// Global variables (950-969)
// ═══════════════════════════════════════════════════════════════════════

g_zero_int  : int
g_const_int : int = 42
g_const_f64 : f64 = 3.14
g_const_bool: bool = true
g_mut_int   : int = 100

read_global :: proc() -> int {
	return g_const_int
}

write_global :: proc(val: int) {
	g_mut_int = val
}

test_globals :: proc() {
	// Zero-init global
	check(g_zero_int == 0, 950)

	// Constant-init int
	check(g_const_int == 42, 951)

	// Constant-init float
	check(g_const_f64 > 3.13, 952)
	check(g_const_f64 < 3.15, 953)

	// Constant-init bool
	check(g_const_bool, 954)

	// Global mutation
	check(g_mut_int == 100, 955)
	g_mut_int = 200
	check(g_mut_int == 200, 956)

	// Global across function calls
	check(read_global() == 42, 957)
	write_global(999)
	check(g_mut_int == 999, 958)

	// Zero-init global mutation
	g_zero_int = 77
	check(g_zero_int == 77, 959)
}

// ═══════════════════════════════════════════════════════════════════════
// Ternary / implicit selector / selector call / ternary when (1000-1039)
// ═══════════════════════════════════════════════════════════════════════

Direction :: enum {
	North,
	South,
	East,
	West,
}

direction_value :: proc(d: Direction) -> int {
	switch d {
	case .North: return 1
	case .South: return 2
	case .East:  return 3
	case .West:  return 4
	}
	return 0
}

identity :: proc(x: int) -> int { return x }

test_ternary_if :: proc() {
	// Trivial scalar path: both arms are constants → SELECT
	a := 10 if true else 20
	check(a == 10, 1000)
	b := 10 if false else 20
	check(b == 20, 1001)

	// Trivial with identifiers → SELECT
	x := 42
	y := 99
	c := x if true else y
	check(c == 42, 1002)
	d := x if false else y
	check(d == 99, 1003)

	// Variable condition → SELECT (trivial arms)
	flag := true
	e := 1 if flag else 0
	check(e == 1, 1004)
	flag = false
	f := 1 if flag else 0
	check(f == 0, 1005)

	// General path: function calls in arms (non-trivial, needs branch)
	g := identity(7) if true else identity(13)
	check(g == 7, 1006)
	h := identity(7) if false else identity(13)
	check(h == 13, 1007)

	// Nested ternary
	val := 100
	r := 1 if val > 50 else (2 if val > 25 else 3)
	check(r == 1, 1008)
	val = 30
	r = 1 if val > 50 else (2 if val > 25 else 3)
	check(r == 2, 1009)
	val = 10
	r = 1 if val > 50 else (2 if val > 25 else 3)
	check(r == 3, 1010)

	// Boolean result
	is_big := true if val > 100 else false
	check(!is_big, 1011)

	// With type conversion (float → int context)
	fi := 5 if true else 10
	check(fi == 5, 1012)
}

test_implicit_selector :: proc() {
	// Implicit selector on enum
	d : Direction = .North
	check(d == Direction.North, 1013)

	d = .West
	check(d == Direction.West, 1014)

	// In function argument (enum)
	v := direction_value(.South)
	check(v == 2, 1015)

	// In comparison
	check(d == .West, 1016)
	check(d != .East, 1017)

	// In switch
	result := 0
	switch d {
	case .North: result = 1
	case .South: result = 2
	case .East:  result = 3
	case .West:  result = 4
	}
	check(result == 4, 1018)
}

test_selector_call :: proc() {
	// SelectorCallExpr: the checker rewrites method-style calls.
	// Test basic call forwarding with a simple call expression.
	r := identity(55)
	check(r == 55, 1019)
}

COMPILE_TIME_FLAG :: true
COMPILE_TIME_VALUE :: 42 when COMPILE_TIME_FLAG else 99

test_ternary_when :: proc() {
	// Compile-time conditional selection
	v := COMPILE_TIME_VALUE
	check(v == 42, 1021)

	// Inline ternary when
	w := 10 when ODIN_OS == .Linux else 20
	check(w == 10, 1022)

	// size_of is compile-time
	s := 8 when size_of(int) == 8 else 4
	check(s == 8, 1023)
}

test_ternary_combined :: proc() {
	// Ternary if with implicit selectors
	d : Direction = .North if true else .South
	check(d == Direction.North, 1024)
	d = .North if false else .South
	check(d == Direction.South, 1025)

	// Ternary if with enum function
	v := direction_value(.East if true else .West)
	check(v == 3, 1026)
	v = direction_value(.East if false else .West)
	check(v == 4, 1027)

	// Chained ternary in loop
	sum := 0
	for i in 0..<6 {
		sum += 1 if i % 2 == 0 else -1
	}
	check(sum == 0, 1028)  // 3 evens (+1) and 3 odds (-1) = 0

	// Ternary as function argument
	check(identity(10 if true else 20) == 10, 1029)
	check(identity(10 if false else 20) == 20, 1030)

	// Multiple ternaries in one expression
	a := (1 if true else 0) + (2 if true else 0) + (4 if false else 0)
	check(a == 3, 1031)
}

// ═══════════════════════════════════════════════════════════════════════
// Type switch (1100-1125)
// ═══════════════════════════════════════════════════════════════════════

TSValue :: union { int, f64, bool }

Circle :: struct { radius: f64 }
Rect   :: struct { w: f64, h: f64 }
Line   :: struct { len: f64 }
Shape  :: union { Circle, Rect, Line }

MaybePtr :: union { ^int }

TSMultiVal :: union { int, f64, string, bool }

ts_classify :: proc(v: TSValue) -> int {
	switch x in v {
	case int:  return 1
	case f64:  return 2
	case bool: return 3
	}
	return 0
}

ts_area_of :: proc(s: Shape) -> f64 {
	switch v in s {
	case Circle: return v.radius * v.radius * 3.14159
	case Rect:   return v.w * v.h
	case Line:   return 0.0
	}
	return -1.0
}

test_type_switch :: proc() {
	// 1100: basic dispatch
	v1: TSValue = 42
	result := 0
	switch x in v1 {
	case int:  result = x
	case f64:  result = -1
	case bool: result = -2
	}
	check(result == 42, 1100)

	v2: TSValue = 3.14
	result = 0
	switch x in v2 {
	case int:  result = -1
	case f64:  result = 1 if x > 3.0 else 0
	case bool: result = -2
	}
	check(result == 1, 1101)

	v3: TSValue = true
	result = 0
	switch x in v3 {
	case int:  result = -1
	case f64:  result = -2
	case bool: result = 1 if x else 0
	}
	check(result == 1, 1102)

	// 1103: default case
	v4: TSValue = 42
	result = 0
	#partial switch x in v4 {
	case f64:  result = -1
	case bool: result = -2
	case:      result = 99
	}
	check(result == 99, 1103)

	// 1104: nil case (uninitialized union → default)
	v5: TSValue
	result = 0
	switch x in v5 {
	case int:  result = -1
	case f64:  result = -2
	case bool: result = -3
	case:      result = 55
	}
	check(result == 55, 1104)

	// 1105: maybe-pointer union
	n := 10
	mp: MaybePtr = &n
	result = 0
	switch p in mp {
	case ^int: result = p^
	case:      result = -1
	}
	check(result == 10, 1105)

	mp2: MaybePtr
	result = 0
	switch p in mp2 {
	case ^int: result = -1
	case:      result = 33
	}
	check(result == 33, 1106)

	// 1107: by-value binding (mutation to union doesn't affect case var)
	v6: TSValue = 42
	result = 0
	switch x in v6 {
	case int:
		v6 = 999.0
		result = x
	case f64:
		result = -1
	case bool:
		result = -2
	}
	check(result == 42, 1107)

	// 1108: by-reference binding
	v7: TSValue = 42
	switch &x in v7 {
	case int:
		x = 100
	case f64:
	case bool:
	}
	val, ok := v7.(int)
	check(ok, 1108)
	check(val == 100, 1109)

	// 1110: #partial switch
	v8: TSMultiVal = 42
	result = 0
	#partial switch x in v8 {
	case int: result = x
	}
	check(result == 42, 1110)

	// 1111: return from type switch function
	fv1: TSValue = 42
	fv2: TSValue = 3.14
	fv3: TSValue = true
	check(ts_classify(fv1) == 1, 1111)
	check(ts_classify(fv2) == 2, 1112)
	check(ts_classify(fv3) == 3, 1113)

	// 1114: struct variants
	s1: Shape = Circle{5.0}
	result = 0
	switch v in s1 {
	case Circle: result = 1 if v.radius == 5.0 else 0
	case Rect:   result = -1
	case Line:   result = -2
	}
	check(result == 1, 1114)

	s2: Shape = Rect{3.0, 4.0}
	result = 0
	switch v in s2 {
	case Circle: result = -1
	case Rect:   result = 1 if v.w == 3.0 && v.h == 4.0 else 0
	case Line:   result = -2
	}
	check(result == 1, 1115)

	// 1116: struct by-reference + struct type assertion
	s3: Shape = Circle{5.0}
	switch &v in s3 {
	case Circle:
		v.radius = 10.0
	case Rect:
	case Line:
	}
	c3, ok3 := s3.(Circle)
	check(ok3, 1116)
	check(c3.radius == 10.0, 1117)

	// 1118: struct type assertion (multi-field)
	s4: Shape = Rect{3.0, 4.0}
	r2, ok4 := s4.(Rect)
	check(ok4, 1118)
	check(r2.w == 3.0, 1119)
	check(r2.h == 4.0, 1120)

	// 1121: type switch in function with struct variants
	c: Shape = Circle{1.0}
	a := ts_area_of(c)
	check(a > 3.14, 1121)
	check(a < 3.15, 1122)

	r: Shape = Rect{3.0, 4.0}
	check(ts_area_of(r) == 12.0, 1123)

	// 1124: type switch in loop
	values := [3]TSValue{ 10, 3.14, true }
	int_sum := 0
	count := 0
	for i := 0; i < 3; i += 1 {
		switch x in values[i] {
		case int:
			int_sum += x
		case f64:
		case bool:
		}
		count += 1
	}
	check(int_sum == 10, 1124)
	check(count == 3, 1125)

	// 1126: labeled break with nested if (regression test)
	v9: TSValue = 42
	result = 0
	outer: switch x in v9 {
	case int:
		if x > 10 {
			result = 1
			break outer
		}
		result = -1
	case f64:
		result = -2
	case bool:
		result = -3
	}
	check(result == 1, 1126)

	// 1127: labeled break with nested if in regular switch (regression test)
	result = 0
	outer2: switch {
	case 42 > 0:
		if 42 > 10 {
			result = 1
			break outer2
		}
		result = -1
	case:
		result = -2
	}
	check(result == 1, 1127)
}

// ═══════════════════════════════════════════════════════════════════════
// any type construction (1200-1219)
// ═══════════════════════════════════════════════════════════════════════

any_check_not_nil :: proc(a: any) -> bool {
	return a.data != nil
}

any_read_int :: proc(a: any) -> int {
	ip := (^int)(a.data)
	return ip^
}

test_any :: proc() {
	// 1200: box int to any, read back through data pointer
	x: int = 42
	a: any = x
	check(a.data != nil, 1200)
	ip := (^int)(a.data)
	check(ip^ == 42, 1201)

	// 1202: box bool to any
	flag := true
	b: any = flag
	bp := (^bool)(b.data)
	check(bp^, 1202)

	// 1203: box float to any
	f := 3.14
	c: any = f
	fp := (^f64)(c.data)
	check(fp^ > 3.0, 1203)
	check(fp^ < 3.2, 1204)

	// 1205: nil any (zero-initialized)
	d: any
	check(d.data == nil, 1205)

	// 1206: same-type any values share typeid
	y: int = 99
	e: any = y
	check(a.id == e.id, 1206)

	// 1207: different-type any values have different typeid
	check(a.id != c.id, 1207)

	// 1208: pass any to function, read fields there
	g: any = x
	check(any_check_not_nil(g), 1208)
	check(any_read_int(g) == 42, 1209)

	// 1210: box small signed types (tests ICONST masking for narrow types)
	b8: i8 = -1
	a_b8: any = b8
	check((^i8)(a_b8.data)^ == -1, 1210)

	i16v: i16 = -1234
	a_i16: any = i16v
	check((^i16)(a_i16.data)^ == -1234, 1211)

	// 1212: any from struct
	s := Circle{5.0}
	a_s: any = s
	check(a_s.data != nil, 1212)
	sp := (^Circle)(a_s.data)
	check(sp.radius == 5.0, 1213)

	// 1214: any from string
	str := "hello"
	a_str: any = str
	check(a_str.data != nil, 1214)
	sp_str := (^string)(a_str.data)
	check(len(sp_str^) == 5, 1215)
}

// ═══════════════════════════════════════════════════════════════════════
// Signed narrow types — equality of negative i8, i16, i32 values
// ═══════════════════════════════════════════════════════════════════════

test_signed_narrow :: proc() {
	// i8 negative values
	a8: i8 = -1
	check(a8 == -1, 1300)
	b8: i8 = -128
	check(b8 == -128, 1301)
	c8: i8 = 127
	check(c8 == 127, 1302)

	// i16 negative values
	a16: i16 = -1
	check(a16 == -1, 1303)
	b16: i16 = -1234
	check(b16 == -1234, 1304)
	c16: i16 = -32768
	check(c16 == -32768, 1305)
	d16: i16 = 32767
	check(d16 == 32767, 1306)

	// i32 negative values
	a32: i32 = -1
	check(a32 == -1, 1307)
	b32: i32 = -2147483648
	check(b32 == -2147483648, 1308)
	c32: i32 = 2147483647
	check(c32 == 2147483647, 1309)

	// Via pointer (tests LOAD + CMP consistency)
	p8 := &a8
	check(p8^ == -1, 1310)
	p16 := &a16
	check(p16^ == -1, 1311)
	p32 := &a32
	check(p32^ == -1, 1312)

	// Negative inequality
	check(a8 != 0, 1313)
	check(a16 != 0, 1314)
	check(a32 != 0, 1315)
}

test_signed_ordering :: proc() {
	// i8: negative < positive
	a8: i8 = -1
	b8: i8 = 1
	check(a8 < b8, 1400)
	check(a8 <= b8, 1401)
	check(b8 > a8, 1402)
	check(b8 >= a8, 1403)
	check(!(a8 > b8), 1404)
	check(!(a8 >= b8), 1405)

	// i8: boundary values
	lo8: i8 = -128
	hi8: i8 = 127
	check(lo8 < hi8, 1406)
	check(hi8 > lo8, 1407)

	// i16: negative < positive
	a16: i16 = -100
	b16: i16 = 100
	check(a16 < b16, 1410)
	check(a16 <= b16, 1411)
	check(b16 > a16, 1412)
	check(b16 >= a16, 1413)

	// i16: boundary values
	lo16: i16 = -32768
	hi16: i16 = 32767
	check(lo16 < hi16, 1414)
	check(hi16 > lo16, 1415)

	// i32: negative < positive
	a32: i32 = -42
	b32: i32 = 42
	check(a32 < b32, 1420)
	check(a32 <= b32, 1421)
	check(b32 > a32, 1422)
	check(b32 >= a32, 1423)

	// i32: boundary values
	lo32: i32 = -2147483648
	hi32: i32 = 2147483647
	check(lo32 < hi32, 1424)
	check(hi32 > lo32, 1425)

	// i64: negative < positive (should still work, was always 64-bit CMP)
	a64: i64 = -999
	b64: i64 = 999
	check(a64 < b64, 1430)
	check(b64 > a64, 1431)

	// Negative ordering among negatives
	x8: i8 = -10
	y8: i8 = -1
	check(x8 < y8, 1440)
	check(y8 > x8, 1441)

	x16: i16 = -1000
	y16: i16 = -1
	check(x16 < y16, 1442)
	check(y16 > x16, 1443)

	// Via pointer (tests LOAD + signed CMP consistency)
	pa8 := &a8
	check(pa8^ < b8, 1450)
	pa16 := &a16
	check(pa16^ < b16, 1451)
	pa32 := &a32
	check(pa32^ < b32, 1452)
}

test_any_type_switch :: proc() {
	// Basic dispatch: int boxed into any
	v1: any = 42
	result1: i32 = 0
	switch x in v1 {
	case int:
		result1 = 1
	case bool:
		result1 = 2
	case f64:
		result1 = 3
	}
	check(result1 == 1, 1500)

	// Bool dispatch
	v2: any = true
	result2: i32 = 0
	switch x in v2 {
	case int:
		result2 = 1
	case bool:
		result2 = 2
	case f64:
		result2 = 3
	}
	check(result2 == 2, 1501)

	// Float dispatch
	v3: any = 3.14
	result3: i32 = 0
	switch x in v3 {
	case int:
		result3 = 1
	case bool:
		result3 = 2
	case f64:
		result3 = 3
	}
	check(result3 == 3, 1502)

	// Nil any → default case
	v4: any
	result4: i32 = 0
	switch x in v4 {
	case int:
		result4 = 1
	case:
		result4 = 9
	}
	check(result4 == 9, 1503)

	// Read the bound value (by value)
	v5: any = 123
	result5: int = 0
	switch x in v5 {
	case int:
		result5 = x
	}
	check(result5 == 123, 1510)

	// Read a bool value
	v6: any = true
	result6 := false
	switch x in v6 {
	case bool:
		result6 = x
	}
	check(result6, 1511)

	// Read an f64 value
	v7: any = 2.5
	result7: f64 = 0
	switch x in v7 {
	case f64:
		result7 = x
	}
	check(result7 == 2.5, 1512)

	// Unmatched type → default
	v8: any = 42
	result8: i32 = 0
	switch x in v8 {
	case bool:
		result8 = 1
	case f64:
		result8 = 2
	case:
		result8 = 3
	}
	check(result8 == 3, 1520)

	// By-reference: mutate the boxed value
	val9: int = 100
	v9: any = val9
	switch &x in v9 {
	case int:
		x = 200
	}
	// The original val9 was copied into the any, so val9 unchanged.
	check(val9 == 100, 1530)

	// String type in any
	v10: any = "hello"
	result10: i32 = 0
	switch x in v10 {
	case string:
		result10 = 1
		check(len(x) == 5, 1541)
	case int:
		result10 = 2
	}
	check(result10 == 1, 1540)
}

// ═══════════════════════════════════════════════════════════════════════
// String comparison (1600-1649)
// ═══════════════════════════════════════════════════════════════════════

test_string_comparison :: proc() {
	// Equality
	a: string = "hello"
	b: string = "hello"
	c: string = "world"
	d: string = "hell"
	e: string = ""
	f: string = ""

	check(a == b, 1600)      // same content
	check(!(a == c), 1601)   // different content, same length
	check(!(a == d), 1602)   // different length
	check(a != c, 1603)      // != different content
	check(!(a != b), 1604)   // != same content
	check(a != d, 1605)      // != different length
	check(e == f, 1606)      // empty == empty
	check(!(e == a), 1607)   // empty != non-empty
	check(e != a, 1608)      // empty != non-empty via !=

	// Ordering
	check("abc" < "abd", 1610)     // differ at last byte
	check(!("abd" < "abc"), 1611)
	check("abc" < "abcd", 1612)    // prefix is less
	check(!("abcd" < "abc"), 1613)
	check(!("abc" < "abc"), 1614)  // equal is not less
	check("" < "a", 1615)          // empty < non-empty
	check(!("a" < ""), 1616)       // non-empty not < empty
	check(!("" < ""), 1617)        // empty not < empty

	check("abd" > "abc", 1620)
	check(!("abc" > "abd"), 1621)
	check("abcd" > "abc", 1622)
	check(!("abc" > "abcd"), 1623)

	check("abc" <= "abd", 1630)
	check("abc" <= "abc", 1631)    // equal satisfies <=
	check(!("abd" <= "abc"), 1632)
	check("" <= "", 1633)          // empty <= empty
	check("abc" <= "abcd", 1634)   // prefix <= longer

	check("abd" >= "abc", 1640)
	check("abc" >= "abc", 1641)    // equal satisfies >=
	check(!("abc" >= "abd"), 1642)
	check("" >= "", 1643)          // empty >= empty
	check("abcd" >= "abc", 1644)   // longer >= prefix

	// Comparison via variable (not just constants)
	s1: string = "apple"
	s2: string = "banana"
	check(s1 < s2, 1645)
	check(s2 > s1, 1646)
	check(s1 != s2, 1647)
}

// ═══════════════════════════════════════════════════════════════════════
// Procedure values and indirect calls (1700-1730)
// ═══════════════════════════════════════════════════════════════════════

// Helper procs for proc value tests (add/mul already defined above)
apply :: proc(f: proc(int, int) -> int, a: int, b: int) -> int {
	return f(a, b)
}

double_it :: proc(x: int) -> int { return x * 2 }
triple_it :: proc(x: int) -> int { return x * 3 }

BinOp :: struct {
	op: proc(int, int) -> int,
	tag: int,
}

Dispatcher :: struct {
	handler: proc(int) -> int,
	multiplier: int,
}

dispatch :: proc(d: Dispatcher, val: int) -> int {
	return d.handler(val) * d.multiplier
}

test_proc_values :: proc() {
	// 1700: basic indirect call — assign proc to variable, call through it
	f := add
	check(f(3, 4) == 7, 1700)

	// 1701: different proc in same variable type
	g := mul
	check(g(3, 4) == 12, 1701)

	// 1702: proc pointer equality
	f2 := add
	check(f == f2, 1702)

	// 1703: proc pointer inequality
	check(f != g, 1703)

	// 1704: reassign proc variable and call through new value
	h := add
	check(h(2, 3) == 5, 1704)
	h = mul
	check(h(2, 3) == 6, 1705)
	h = add
	check(h(2, 3) == 5, 1706)

	// 1707: proc as parameter — pass proc value to another function
	check(apply(add, 10, 20) == 30, 1707)
	check(apply(mul, 10, 20) == 200, 1708)

	// 1709: nested call — result of indirect call used in another
	r := apply(add, apply(mul, 3, 4), 5)
	check(r == 17, 1709)  // mul(3,4)=12, add(12,5)=17

	// 1710: proc value from conditional
	op := add if true else mul
	check(op(5, 6) == 11, 1710)

	// 1711: struct with proc field — compound lit init
	bo := BinOp{ op = add, tag = 1 }
	check(bo.op(10, 20) == 30, 1711)
	check(bo.tag == 1, 1712)

	// 1713: struct proc field mutation
	bo.op = mul
	check(bo.op(10, 20) == 200, 1713)

	// 1717: nil comparison — zero-init proc is nil
	np: proc(int, int) -> int
	check(np == nil, 1717)

	// 1718: assign then compare non-nil
	np = add
	check(np != nil, 1718)

	// 1719: compare against nil after assignment
	check(!(np == nil), 1719)

	// 1720: reset to nil
	np = nil
	check(np == nil, 1720)

	// 1721: allocator-like pattern — struct with handler and data, dispatch
	d1 := Dispatcher{ handler = double_it, multiplier = 3 }
	check(dispatch(d1, 5) == 30, 1721)  // double_it(5)=10, 10*3=30

	d2 := Dispatcher{ handler = triple_it, multiplier = 2 }
	check(dispatch(d2, 5) == 30, 1722)  // triple_it(5)=15, 15*2=30

	// 1723: different values yield different results
	check(dispatch(d1, 10) == 60, 1723)  // double_it(10)=20, 20*3=60
	check(dispatch(d2, 10) == 60, 1724)  // triple_it(10)=30, 30*2=60

	// 1725: swap handler at runtime
	d1.handler = triple_it
	check(dispatch(d1, 5) == 45, 1725)  // triple_it(5)=15, 15*3=45

	// 1726: pass struct by value — original unaffected
	d3 := Dispatcher{ handler = double_it, multiplier = 1 }
	check(dispatch(d3, 7) == 14, 1726)  // double_it(7)=14, 14*1=14

	// 1730: loop with dynamic proc selection
	sum := 0
	for i := 0; i < 6; i += 1 {
		op2 := add if i % 2 == 0 else mul
		sum += op2(i, 2)
	}
	// i=0: add(0,2)=2; i=1: mul(1,2)=2; i=2: add(2,2)=4;
	// i=3: mul(3,2)=6; i=4: add(4,2)=6; i=5: mul(5,2)=10
	// sum = 2+2+4+6+6+10 = 30
	check(sum == 30, 1730)
}

// ═══════════════════════════════════════════════════════════════════════
// Main — run everything
// ═══════════════════════════════════════════════════════════════════════

main :: proc() {
	print_msg("  branch_spill...\n")
	test_branch_spill()
	print_msg("  multi_branch...\n")
	test_multi_branch()
	print_msg("  nested_if...\n")
	test_nested_if()
	print_msg("  for_loop...\n")
	test_for_loop()
	print_msg("  nested_loop...\n")
	test_nested_loop()
	print_msg("  call_across_branch...\n")
	test_call_across_branch()
	print_msg("  break_continue...\n")
	test_break_continue()
	print_msg("  early_return...\n")
	check(test_early_return() == 7, 169)
	print_msg("  multi_return...\n")
	test_multi_return()
	print_msg("  float...\n")
	test_float()
	print_msg("  range_int...\n")
	test_range_int()
	print_msg("  range_array...\n")
	test_range_array()
	print_msg("  range_index...\n")
	test_range_index()
	print_msg("  nested_range...\n")
	test_nested_range()
	print_msg("  bool_logic...\n")
	test_bool_logic()
	print_msg("  stress...\n")
	test_stress()
	print_msg("  strings...\n")
	test_strings()
	print_msg("  switch_basic...\n")
	test_switch_basic()
	print_msg("  switch_features...\n")
	test_switch_features()
	print_msg("  switch_advanced...\n")
	test_switch_advanced()
	print_msg("  slicing...\n")
	test_slicing()
	print_msg("  or_else...\n")
	test_or_else()
	print_msg("  globals...\n")
	test_globals()
	print_msg("  ternary_if...\n")
	test_ternary_if()
	print_msg("  implicit_selector...\n")
	test_implicit_selector()
	print_msg("  selector_call...\n")
	test_selector_call()
	print_msg("  ternary_when...\n")
	test_ternary_when()
	print_msg("  ternary_combined...\n")
	test_ternary_combined()
	print_msg("  type_switch...\n")
	test_type_switch()
	print_msg("  any...\n")
	test_any()
	print_msg("  signed_narrow...\n")
	test_signed_narrow()
	print_msg("  signed_ordering...\n")
	test_signed_ordering()
	print_msg("  any_type_switch...\n")
	test_any_type_switch()
	print_msg("  string_comparison...\n")
	test_string_comparison()
	print_msg("  proc_values...\n")
	test_proc_values()
	print_msg("ALL PASS\n")
	exit(0)
}
