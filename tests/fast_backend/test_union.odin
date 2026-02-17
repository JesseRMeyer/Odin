package test_union

foreign import libc "system:c"
foreign libc {
	write :: proc "c" (fd: i32, buf: rawptr, count: int) -> int ---
	abort :: proc "c" () -> ! ---
}

check :: proc(ok: bool, id: int) {
	if !ok {
		msg := "FAIL\n"
		write(2, raw_data(msg), len(msg))
		abort()
	}
}

Value :: union { int, f64, bool }

main :: proc() {
	// 1100: basic union creation and type assertion
	v: Value = 42
	x, ok := v.(int)
	check(ok, 1100)
	check(x == 42, 1101)

	// 1102: wrong variant returns false
	_, ok2 := v.(f64)
	check(!ok2, 1102)

	// 1103: nil union
	v2: Value
	_, ok3 := v2.(int)
	check(!ok3, 1103)

	// 1104: float variant
	v3: Value = 3.14
	y, ok4 := v3.(f64)
	check(ok4, 1104)

	// 1105: bool variant
	v4: Value = true
	z, ok5 := v4.(bool)
	check(ok5, 1105)
	check(z, 1106)

	// 1107: reassignment changes tag
	v = 2.718
	_, ok6 := v.(int)
	check(!ok6, 1107)
	w, ok7 := v.(f64)
	check(ok7, 1108)

	// 1109: direct type assertion (should not trap)
	v = 99
	val := v.(int)
	check(val == 99, 1109)

	// 1110: union as function parameter/return
	check(get_val(v) == 99, 1110)

	// 1111: maybe-pointer union
	MaybePtr :: union { ^int }
	n := 10
	mp: MaybePtr = &n
	p, ok8 := mp.(^int)
	check(ok8, 1111)
	check(p^ == 10, 1112)

	// 1113: nil maybe-pointer
	mp2: MaybePtr
	_, ok9 := mp2.(^int)
	check(!ok9, 1113)

	pass := "PASS\n"
	write(1, raw_data(pass), len(pass))
}

get_val :: proc(v: Value) -> int {
	x, ok := v.(int)
	if ok { return x }
	return -1
}
