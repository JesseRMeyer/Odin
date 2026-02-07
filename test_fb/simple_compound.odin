package simple_compound

Vec2 :: struct {
	x: int,
	y: int,
}

test_read :: proc() -> int {
	v := Vec2{x = 10, y = 20}
	return v.x + v.y
}

main :: proc() {
	r := test_read()
	_ = r
}
