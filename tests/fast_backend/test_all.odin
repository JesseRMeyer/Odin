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
	print_msg("ALL PASS\n")
	exit(0)
}
