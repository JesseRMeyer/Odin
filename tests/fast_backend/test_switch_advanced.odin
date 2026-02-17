package test_switch_advanced

foreign import libc "system:c"
foreign libc {
	exit :: proc "c" (code: i32) ---
}

check :: proc(cond: bool, code: i32) {
	if !cond {
		exit(code)
	}
}

// Test: range cases (forces non-trivial path)
grade :: proc(score: int) -> int {
	switch {
	case score >= 90:
		return 4
	case score >= 80:
		return 3
	case score >= 70:
		return 2
	case score >= 60:
		return 1
	case:
		return 0
	}
}

test_range_switch :: proc() {
	check(grade(95) == 4, 1)
	check(grade(85) == 3, 2)
	check(grade(75) == 2, 3)
	check(grade(65) == 1, 4)
	check(grade(50) == 0, 5)
}

// Test: switch with no matching case and no default
test_no_match :: proc() {
	x := 42
	result := -1
	switch x {
	case 1:
		result = 1
	case 2:
		result = 2
	case 3:
		result = 3
	}
	check(result == -1, 10)  // no case matched, result unchanged
}

// Test: single case switch
test_single_case :: proc() {
	x := 5
	result := 0
	switch x {
	case 5:
		result = 50
	}
	check(result == 50, 15)
}

// Test: fallthrough chain
test_fallthrough_chain :: proc() {
	x := 1
	result := 0
	switch x {
	case 1:
		result += 1
		fallthrough
	case 2:
		result += 10
		fallthrough
	case 3:
		result += 100
	}
	// 1 -> fallthrough to 2 -> fallthrough to 3 = 1+10+100 = 111
	check(result == 111, 20)
}

// Test: switch over bool
test_bool_switch :: proc() {
	b := true
	result := 0
	switch b {
	case true:
		result = 1
	case false:
		result = 2
	}
	check(result == 1, 25)

	b = false
	result = 0
	switch b {
	case true:
		result = 1
	case false:
		result = 2
	}
	check(result == 2, 26)
}

// Test: complex control flow - switch inside switch inside loop
test_complex :: proc() {
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
		case 1:
			total += 100
		case 2:
			total += 1000
		}
	}
	// i=0: 1+2+4=7, i=1: 100, i=2: 1000 = 1107
	check(total == 1107, 30)
}

// Test: default case in middle (not last)
test_default_middle :: proc() {
	x := 99
	result := 0
	switch x {
	case 1:
		result = 1
	case:
		result = -1
	case 2:
		result = 2
	}
	check(result == -1, 35)
}

// Test: empty case body
test_empty_case :: proc() {
	x := 2
	result := 10
	switch x {
	case 1:
		result = 1
	case 2:
		// empty body
	case 3:
		result = 3
	}
	check(result == 10, 40)  // result unchanged
}

main :: proc() {
	test_range_switch()
	test_no_match()
	test_single_case()
	test_fallthrough_chain()
	test_bool_switch()
	test_complex()
	test_default_middle()
	test_empty_case()
	exit(0)
}
