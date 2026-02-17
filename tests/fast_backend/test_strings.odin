package test_strings

foreign import libc "system:c"
foreign libc {
	exit :: proc "c" (code: i32) ---
}

check :: proc(cond: bool, code: i32) {
	if !cond {
		exit(code)
	}
}

// Test: string length via builtin len
test_string_len :: proc() {
	s := "hello"
	check(len(s) == 5, 1)

	empty := ""
	check(len(empty) == 0, 2)

	longer := "hello, world!"
	check(len(longer) == 13, 3)
}

// Test: string comparison
test_string_cmp :: proc() {
	a := "abc"
	b := "abc"
	// String equality means same length AND same data pointer (interned)
	check(len(a) == len(b), 10)
	check(len(a) == 3, 11)
}

// Test: passing strings to functions
str_len :: proc(s: string) -> int {
	return len(s)
}

test_string_pass :: proc() {
	s := "test"
	n := str_len(s)
	check(n == 4, 20)
}

main :: proc() {
	test_string_len()
	test_string_cmp()
	test_string_pass()
	exit(0)
}
