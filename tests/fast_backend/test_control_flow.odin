package test_control_flow

foreign import libc "system:c"
foreign libc {
	exit :: proc "c" (code: i32) ---
}

check :: proc(cond: bool, code: i32) {
	if !cond {
		exit(code)
	}
}

add :: proc(a: int, b: int) -> int {
	return a + b
}

mul :: proc(a: int, b: int) -> int {
	return a * b
}

// Test: multiple branches
test_multi_branch :: proc() {
	a := 10
	b := 20
	c := a + b
	check(c == 30, 1)
	d := c * 2
	check(d == 60, 2)
	e := d - a
	check(e == 50, 3)
	f := e / 5
	check(f == 10, 4)
}

// Test: nested if/else
test_nested_if :: proc() {
	x := 42
	if x > 0 {
		if x > 100 {
			exit(10)
		} else {
			check(x == 42, 11)
		}
	} else {
		exit(12)
	}
}

// Test: for loop
test_for_loop :: proc() {
	sum := 0
	for i := 0; i < 10; i += 1 {
		sum += i
	}
	check(sum == 45, 20)
}

// Test: nested for loops
test_nested_loop :: proc() {
	total := 0
	for i := 0; i < 5; i += 1 {
		for j := 0; j < 3; j += 1 {
			total += 1
		}
	}
	check(total == 15, 30)
}

// Test: function calls across branches
test_call_across_branch :: proc() {
	a := add(3, 4)
	check(a == 7, 40)
	b := mul(a, 3)
	check(b == 21, 41)
	c := add(b, a)
	check(c == 28, 42)
}

// Test: break and continue
test_break_continue :: proc() {
	sum := 0
	for i := 0; i < 20; i += 1 {
		if i == 10 { break }
		if i % 2 == 0 { continue }
		sum += i
	}
	// Odd numbers 1..9: 1+3+5+7+9 = 25
	check(sum == 25, 50)
}

// Test: early return
test_early_return :: proc() -> int {
	for i := 0; i < 100; i += 1 {
		if i == 7 { return i }
	}
	return -1
}

main :: proc() {
	test_multi_branch()
	test_nested_if()
	test_for_loop()
	test_nested_loop()
	test_call_across_branch()
	test_break_continue()
	r := test_early_return()
	check(r == 7, 60)
	exit(0)
}
