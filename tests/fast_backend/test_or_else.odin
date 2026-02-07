package test_or_else

foreign import libc "system:c"
foreign libc {
	exit :: proc "c" (code: i32) ---
}

check :: proc(cond: bool, code: i32) {
	if !cond {
		exit(code)
	}
}

// Helper: return (value, ok)
try_get :: proc(ok: bool, val: int) -> (int, bool) {
	return val, ok
}

// Test 1: or_else with success
test_or_else_success :: proc() {
	x := try_get(true, 42) or_else 99
	check(x == 42, 1)
}

// Test 2: or_else with failure
test_or_else_failure :: proc() {
	x := try_get(false, 0) or_else 99
	check(x == 99, 2)
}

// Test 3: or_else in a loop
test_or_else_loop :: proc() {
	sum := 0
	for i := 0; i < 5; i += 1 {
		val := try_get(i < 3, i * 10) or_else -1
		sum += val
	}
	// i=0: 0, i=1: 10, i=2: 20, i=3: -1, i=4: -1 = 28
	check(sum == 28, 3)
}

// Test 4: or_else with function call fallback
fallback :: proc() -> int {
	return 777
}

test_or_else_call_fallback :: proc() {
	x := try_get(false, 0) or_else fallback()
	check(x == 777, 4)
}

// Test 5: chained or_else
test_chained :: proc() {
	x := try_get(false, 0) or_else 100
	y := try_get(true, x) or_else 200
	check(y == 100, 5)
}

main :: proc() {
	test_or_else_success()
	test_or_else_failure()
	test_or_else_loop()
	test_or_else_call_fallback()
	test_chained()
	exit(0)
}
