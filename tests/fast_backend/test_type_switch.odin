package test_type_switch

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

// ── Types ──

Value :: union { int, f64, bool }
Shape :: union { Circle, Rect, Line }

Circle :: struct { radius: f64 }
Rect   :: struct { w: f64, h: f64 }
Line   :: struct { len: f64 }

MaybePtr :: union { ^int }

NilableValue :: union { int, string }

ZeroVariant :: union { struct {} }

MultiVal :: union { int, f64, string, bool }

// ── Tests ──

// 1100: basic dispatch — each variant dispatched correctly
test_basic_dispatch :: proc() {
	v1: Value = 42
	result := 0
	switch x in v1 {
	case int:  result = x
	case f64:  result = -1
	case bool: result = -2
	}
	check(result == 42, 1100)

	v2: Value = 3.14
	result = 0
	switch x in v2 {
	case int:  result = -1
	case f64:  result = 1 if x > 3.0 else 0
	case bool: result = -2
	}
	check(result == 1, 1101)

	v3: Value = true
	result = 0
	switch x in v3 {
	case int:  result = -1
	case f64:  result = -2
	case bool: result = 1 if x else 0
	}
	check(result == 1, 1102)
}

// 1103: default case — unmatched variant falls to default
test_default_case :: proc() {
	v: Value = 42
	result := 0
	#partial switch x in v {
	case f64:  result = -1
	case bool: result = -2
	case:      result = 99
	}
	check(result == 99, 1103)

	// Default with no match at all
	v2: Value = true
	result = 0
	#partial switch x in v2 {
	case int: result = 1
	case:     result = 77
	}
	check(result == 77, 1104)
}

// 1105: nil case — uninitialized union matches default (nil tag)
test_nil_case :: proc() {
	v: NilableValue
	result := 0
	switch x in v {
	case int:    result = -1
	case string: result = -2
	case:        result = 55  // default = nil for uninitialized
	}
	check(result == 55, 1105)
}

// 1106: maybe-pointer union dispatch
test_maybe_pointer :: proc() {
	n := 10
	mp: MaybePtr = &n
	result := 0
	switch p in mp {
	case ^int: result = p^
	case:      result = -1
	}
	check(result == 10, 1106)

	// nil maybe-pointer goes to default
	mp2: MaybePtr
	result = 0
	switch p in mp2 {
	case ^int: result = -1
	case:      result = 33
	}
	check(result == 33, 1107)
}

// 1108: by-value binding — mutations to union don't affect case variable
test_by_value :: proc() {
	v: Value = 42
	result := 0
	switch x in v {
	case int:
		// mutate union: overwrite with a float — different variant
		v = 999.0
		result = x  // x should still be 42 (copied before mutation)
	case f64:
		result = -1
	case bool:
		result = -2
	}
	check(result == 42, 1108)
}

// 1109: by-reference binding — mutations through case variable visible
test_by_reference :: proc() {
	v: Value = 42
	switch &x in v {
	case int:
		x = 100
	case f64:
	case bool:
	}
	// After by-ref switch, union data should be changed
	val, ok := v.(int)
	check(ok, 1109)
	check(val == 100, 1110)
}

// 1111: #partial switch — subset of variants
test_partial :: proc() {
	v: MultiVal = 42
	result := 0
	#partial switch x in v {
	case int: result = x
	}
	check(result == 42, 1111)

	// Non-matching partial just falls through
	v2: MultiVal = true
	result = 0
	#partial switch x in v2 {
	case int: result = -1
	case f64: result = -2
	}
	check(result == 0, 1112)
}

// 1113: labeled break (including nested if)
test_labeled_break :: proc() {
	v: Value = 42
	result := 0
	outer: switch x in v {
	case int:
		if x > 10 {
			result = 1
			break outer
		}
		result = -1
	case f64:
		result = -2
	case bool:
		result = -3
	}
	check(result == 1, 1113)
}

// 1114: nested type switch inside loop with break
test_nested_loop :: proc() {
	values := [3]Value{ 10, 3.14, true }
	int_sum := 0
	count := 0
	for i := 0; i < 3; i += 1 {
		switch x in values[i] {
		case int:
			int_sum += x
		case f64:
			// skip
		case bool:
			// skip
		}
		count += 1
	}
	check(int_sum == 10, 1114)
	check(count == 3, 1115)
}

// 1116: return from within type switch
classify_value :: proc(v: Value) -> int {
	switch x in v {
	case int:  return 1
	case f64:  return 2
	case bool: return 3
	}
	return 0  // nil
}

test_return_from_switch :: proc() {
	v1: Value = 42
	v2: Value = 3.14
	v3: Value = true
	check(classify_value(v1) == 1, 1116)
	check(classify_value(v2) == 2, 1117)
	check(classify_value(v3) == 3, 1118)
}

// 1119: struct variants
test_struct_variants :: proc() {
	s1: Shape = Circle{5.0}
	result := 0
	switch v in s1 {
	case Circle: result = 1 if v.radius == 5.0 else 0
	case Rect:   result = -1
	case Line:   result = -2
	}
	check(result == 1, 1119)

	s2: Shape = Rect{3.0, 4.0}
	result = 0
	switch v in s2 {
	case Circle: result = -1
	case Rect:   result = 1 if v.w == 3.0 && v.h == 4.0 else 0
	case Line:   result = -2
	}
	check(result == 1, 1120)
}

// 1121: by-reference with structs — mutate through ref
test_struct_by_ref :: proc() {
	s: Shape = Circle{5.0}
	switch &v in s {
	case Circle:
		v.radius = 10.0
	case Rect:
	case Line:
	}
	c, ok := s.(Circle)
	check(ok, 1121)
	check(c.radius == 10.0, 1122)
}

// 1123: type switch in a function with struct return
area_of :: proc(s: Shape) -> f64 {
	switch v in s {
	case Circle: return v.radius * v.radius * 3.14159
	case Rect:   return v.w * v.h
	case Line:   return 0.0
	}
	return -1.0
}

test_function_with_switch :: proc() {
	c: Shape = Circle{1.0}
	a := area_of(c)
	check(a > 3.14, 1123)
	check(a < 3.15, 1124)

	r: Shape = Rect{3.0, 4.0}
	check(area_of(r) == 12.0, 1125)
}

// ── Main ──

main :: proc() {
	print_msg("  basic_dispatch...\n")
	test_basic_dispatch()
	print_msg("  default_case...\n")
	test_default_case()
	print_msg("  nil_case...\n")
	test_nil_case()
	print_msg("  maybe_pointer...\n")
	test_maybe_pointer()
	print_msg("  by_value...\n")
	test_by_value()
	print_msg("  by_reference...\n")
	test_by_reference()
	print_msg("  partial...\n")
	test_partial()
	print_msg("  labeled_break...\n")
	test_labeled_break()
	print_msg("  nested_loop...\n")
	test_nested_loop()
	print_msg("  return_from_switch...\n")
	test_return_from_switch()
	print_msg("  struct_variants...\n")
	test_struct_variants()
	print_msg("  struct_by_ref...\n")
	test_struct_by_ref()
	print_msg("  function_with_switch...\n")
	test_function_with_switch()
	print_msg("TYPE SWITCH ALL PASS\n")
	exit(0)
}
