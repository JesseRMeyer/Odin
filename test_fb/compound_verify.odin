package compound_verify

foreign import libc "system:c"
foreign libc {
	exit :: proc "c" (status: i32) -> ! ---
}

Vec2 :: struct {
	x: int,
	y: int,
}

Rect :: struct {
	min: Vec2,
	max: Vec2,
}

main :: proc() {
	// Test 1: Named fields
	v1 := Vec2{x = 10, y = 20}
	if v1.x + v1.y != 30 { exit(1) }

	// Test 2: Positional fields
	v2 := Vec2{3, 7}
	if v2.x + v2.y != 10 { exit(2) }

	// Test 3: Empty struct (zero-initialized)
	v3 := Vec2{}
	if v3.x + v3.y != 0 { exit(3) }

	// Test 4: Partial init (y zero-initialized)
	v4 := Vec2{x = 42}
	if v4.x + v4.y != 42 { exit(4) }

	// Test 5: Array literal
	a := [3]int{10, 20, 30}
	if a[0] + a[1] + a[2] != 60 { exit(5) }

	// Test 6: Nested struct
	r := Rect{min = Vec2{x = 1, y = 2}, max = Vec2{x = 3, y = 4}}
	if r.min.x + r.min.y + r.max.x + r.max.y != 10 { exit(6) }

	// Test 7: Struct reassignment
	v5 := Vec2{x = 1, y = 2}
	v5 = Vec2{x = 100, y = 200}
	if v5.x + v5.y != 300 { exit(7) }

	// All tests passed — exit 42 as success signal
	exit(42)
}
