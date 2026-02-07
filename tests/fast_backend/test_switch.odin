package test_switch

foreign import libc "system:c"
foreign libc {
	exit :: proc "c" (code: i32) ---
}

check :: proc(cond: bool, code: i32) {
	if !cond {
		exit(code)
	}
}

// Test 1: basic integer switch with constant cases
test_basic_switch :: proc() {
	x := 2
	result := 0
	switch x {
	case 1:
		result = 10
	case 2:
		result = 20
	case 3:
		result = 30
	}
	check(result == 20, 1)
}

// Test 2: default case
test_default :: proc() {
	x := 99
	result := 0
	switch x {
	case 1:
		result = 10
	case 2:
		result = 20
	case:
		result = -1
	}
	check(result == -1, 2)
}

// Test 3: multiple values per case
test_multi_value :: proc() {
	x := 3
	result := 0
	switch x {
	case 1, 2, 3:
		result = 100
	case 4, 5:
		result = 200
	case:
		result = 300
	}
	check(result == 100, 3)
}

// Test 4: tag-less boolean switch
test_tagless :: proc() {
	x := 42
	result := 0
	switch {
	case x < 10:
		result = 1
	case x < 50:
		result = 2
	case x < 100:
		result = 3
	case:
		result = 4
	}
	check(result == 2, 4)
}

// Test 5: switch with break (exits switch)
test_break :: proc() {
	x := 1
	result := 0
	outer: for i := 0; i < 1; i += 1 {
		switch x {
		case 1:
			result = 10
			break outer
		case 2:
			result = 20
		}
		result = 99 // should not execute due to break outer
	}
	check(result == 10, 5)
}

// Test 6: switch with fallthrough
test_fallthrough :: proc() {
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
	check(result == 30, 6)
}

// Test 7: switch with init statement
test_init :: proc() {
	result := 0
	switch y := 5; y {
	case 5:
		result = 50
	case:
		result = -1
	}
	check(result == 50, 7)
}

// Test 8: nested switch
test_nested :: proc() {
	x := 1
	y := 2
	result := 0
	switch x {
	case 1:
		switch y {
		case 1:
			result = 11
		case 2:
			result = 12
		}
	case 2:
		result = 20
	}
	check(result == 12, 8)
}

// Test 9: switch in a loop
test_switch_in_loop :: proc() {
	sum := 0
	for i := 0; i < 5; i += 1 {
		switch i {
		case 0:
			sum += 1
		case 1:
			sum += 10
		case 2:
			sum += 100
		case:
			sum += 1000
		}
	}
	// 1 + 10 + 100 + 1000 + 1000 = 2111
	check(sum == 2111, 9)
}

// Test 10: switch returning from function
classify :: proc(x: int) -> int {
	switch {
	case x < 0:
		return -1
	case x == 0:
		return 0
	case:
		return 1
	}
}

test_switch_return :: proc() {
	check(classify(-5) == -1, 10)
	check(classify(0) == 0, 11)
	check(classify(7) == 1, 12)
}

main :: proc() {
	test_basic_switch()
	test_default()
	test_multi_value()
	test_tagless()
	test_break()
	test_fallthrough()
	test_init()
	test_nested()
	test_switch_in_loop()
	test_switch_return()
	exit(0)
}
