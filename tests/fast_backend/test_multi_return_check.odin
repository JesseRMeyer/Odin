package test_multi_return_check

foreign import libc "system:c"
foreign libc {
	exit :: proc "c" (code: i32) ---
}

check :: proc(cond: bool, code: i32) {
	if !cond {
		exit(code)
	}
}

two_vals :: proc() -> (int, bool) {
	return 42, true
}

three_vals :: proc() -> (int, int, bool) {
	return 10, 20, true
}

swap :: proc(a: int, b: int) -> (int, int) {
	return b, a
}

main :: proc() {
	a, ok := two_vals()
	check(a == 42, 1)
	check(ok, 2)

	x, y, ok2 := three_vals()
	check(x == 10, 3)
	check(y == 20, 4)
	check(ok2, 5)

	p, q := swap(100, 200)
	check(p == 200, 6)
	check(q == 100, 7)

	// Reassignment
	a, ok = two_vals()
	check(a == 42, 8)
	check(ok, 9)

	// Blank identifiers
	_, ok3 := two_vals()
	check(ok3, 10)

	v, _ := swap(5, 6)
	check(v == 6, 11)

	exit(0)
}
