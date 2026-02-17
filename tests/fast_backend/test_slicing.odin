package test_slicing

foreign import libc "system:c"
foreign libc {
	exit :: proc "c" (code: i32) ---
}

check :: proc(cond: bool, code: i32) {
	if !cond {
		exit(code)
	}
}

// Test 1: basic array slicing
test_array_slice :: proc() {
	arr := [5]int{10, 20, 30, 40, 50}
	s := arr[1:4]
	check(len(s) == 3, 1)
	check(s[0] == 20, 2)
	check(s[1] == 30, 3)
	check(s[2] == 40, 4)
}

// Test 2: slice the whole array
test_full_slice :: proc() {
	arr := [3]int{1, 2, 3}
	s := arr[:]
	check(len(s) == 3, 10)
	check(s[0] == 1, 11)
	check(s[2] == 3, 12)
}

// Test 3: slice with only low bound
test_low_only :: proc() {
	arr := [4]int{10, 20, 30, 40}
	s := arr[2:]
	check(len(s) == 2, 15)
	check(s[0] == 30, 16)
	check(s[1] == 40, 17)
}

// Test 4: slice with only high bound
test_high_only :: proc() {
	arr := [4]int{10, 20, 30, 40}
	s := arr[:2]
	check(len(s) == 2, 20)
	check(s[0] == 10, 21)
	check(s[1] == 20, 22)
}

// Test 5: slice of a slice
test_slice_of_slice :: proc() {
	arr := [6]int{1, 2, 3, 4, 5, 6}
	s1 := arr[1:5]  // {2, 3, 4, 5}
	s2 := s1[1:3]   // {3, 4}
	check(len(s2) == 2, 25)
	check(s2[0] == 3, 26)
	check(s2[1] == 4, 27)
}

// Test 6: string slicing
test_string_slice :: proc() {
	s := "hello, world"
	sub := s[7:]
	check(len(sub) == 5, 30)
	check(sub[0] == 'w', 31)
	check(sub[4] == 'd', 32)

	sub2 := s[:5]
	check(len(sub2) == 5, 33)
	check(sub2[0] == 'h', 34)
	check(sub2[4] == 'o', 35)
}

// Test 7: empty slice
test_empty_slice :: proc() {
	arr := [3]int{1, 2, 3}
	s := arr[1:1]
	check(len(s) == 0, 40)
}

// Test 8: pass slice to function
sum_slice :: proc(s: []int) -> int {
	total := 0
	for i := 0; i < len(s); i += 1 {
		total += s[i]
	}
	return total
}

test_pass_slice :: proc() {
	arr := [4]int{10, 20, 30, 40}
	s := arr[1:3]
	result := sum_slice(s)
	check(result == 50, 45)  // 20 + 30
}

// Test 9: slice in a loop
test_slice_in_loop :: proc() {
	arr := [5]int{1, 2, 3, 4, 5}
	total := 0
	for i := 0; i < 4; i += 1 {
		s := arr[i:i+2]
		total += s[0] + s[1]
	}
	// (1+2) + (2+3) + (3+4) + (4+5) = 3+5+7+9 = 24
	check(total == 24, 50)
}

main :: proc() {
	test_array_slice()
	test_full_slice()
	test_low_only()
	test_high_only()
	test_slice_of_slice()
	test_string_slice()
	test_empty_slice()
	test_pass_slice()
	test_slice_in_loop()
	exit(0)
}
