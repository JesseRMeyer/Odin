package test_float_and_range

foreign import libc "system:c"
foreign libc {
	exit :: proc "c" (code: i32) ---
}

check :: proc(cond: bool, code: i32) {
	if !cond {
		exit(code)
	}
}

// Float arithmetic
test_float :: proc() {
	a : f64 = 3.5
	b : f64 = 2.0
	c := a + b
	check(c == 5.5, 1)
	d := a * b
	check(d == 7.0, 2)
	e := a - b
	check(e == 1.5, 3)
	f := a / b
	check(f == 1.75, 4)
}

// Integer range
test_range_int :: proc() {
	sum := 0
	for i in 0..<5 {
		sum += i
	}
	check(sum == 10, 10)
}

// Array iteration
test_range_array :: proc() {
	arr := [4]int{10, 20, 30, 40}
	sum := 0
	for val in arr {
		sum += val
	}
	check(sum == 100, 20)
}

// Range with index
test_range_index :: proc() {
	arr := [3]int{100, 200, 300}
	idx_sum := 0
	val_sum := 0
	for val, idx in arr {
		idx_sum += idx
		val_sum += val
	}
	check(idx_sum == 3, 30)   // 0+1+2
	check(val_sum == 600, 31) // 100+200+300
}

// Nested ranges
test_nested_range :: proc() {
	total := 0
	for i in 0..<3 {
		for j in 0..<4 {
			total += 1
		}
	}
	check(total == 12, 40)
}

// Boolean logic (&&, ||)
test_bool_logic :: proc() {
	a := true
	b := false
	check(a && !b, 50)
	check(a || b, 51)
	check(!(a && b), 52)
	c := 5
	check(c > 3 && c < 10, 53)
}

main :: proc() {
	test_float()
	test_range_int()
	test_range_array()
	test_range_index()
	test_nested_range()
	test_bool_logic()
	exit(0)
}
