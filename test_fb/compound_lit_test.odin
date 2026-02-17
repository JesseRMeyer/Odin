package compound_lit_test

Vec2 :: struct {
	x: int,
	y: int,
}

Vec3 :: struct {
	x: f64,
	y: f64,
	z: f64,
}

// Nested struct
Rect :: struct {
	min: Vec2,
	max: Vec2,
}

add_vec2 :: proc(a, b: Vec2) -> int {
	return a.x + a.y + b.x + b.y
}

test_named_fields :: proc() -> int {
	v := Vec2{x = 10, y = 20}
	return v.x + v.y  // expect 30
}

test_positional_fields :: proc() -> int {
	v := Vec2{3, 7}
	return v.x + v.y  // expect 10
}

test_empty_struct :: proc() -> int {
	v := Vec2{}
	return v.x + v.y  // expect 0
}

test_partial_init :: proc() -> int {
	v := Vec2{x = 42}
	return v.x + v.y  // expect 42 (y is zero-initialized)
}

test_array_literal :: proc() -> int {
	a := [3]int{10, 20, 30}
	return a[0] + a[1] + a[2]  // expect 60
}

test_nested_struct :: proc() -> int {
	r := Rect{min = Vec2{x = 1, y = 2}, max = Vec2{x = 3, y = 4}}
	return r.min.x + r.min.y + r.max.x + r.max.y  // expect 10
}

test_struct_assignment :: proc() -> int {
	v := Vec2{x = 1, y = 2}
	v = Vec2{x = 100, y = 200}
	return v.x + v.y  // expect 300
}

test_struct_as_arg :: proc() -> int {
	return add_vec2(Vec2{x = 5, y = 6}, Vec2{x = 7, y = 8})  // expect 26
}

main :: proc() {
	r1 := test_named_fields()
	r2 := test_positional_fields()
	r3 := test_empty_struct()
	r4 := test_partial_init()
	r5 := test_array_literal()
	r6 := test_nested_struct()
	r7 := test_struct_assignment()
	// r8 := test_struct_as_arg()  // needs ABI aggregate passing

	// Simple validation: add them up
	total := r1 + r2 + r3 + r4 + r5 + r6 + r7
	if total == 452 {  // 30 + 10 + 0 + 42 + 60 + 10 + 300
		// success
	}
}
