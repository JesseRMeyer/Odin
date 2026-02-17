#+feature dynamic-literals
package main

test_min_max :: proc(a, b: int) -> int {
	lo := min(a, b)
	hi := max(a, b)
	return hi - lo
}

test_abs :: proc(x: int) -> int {
	return abs(x)
}

test_clamp :: proc(x, lo, hi: int) -> int {
	return clamp(x, lo, hi)
}

test_len :: proc(p: ^[]int) -> int {
	return len(p^)
}

test_cap :: proc(p: ^[dynamic]int) -> int {
	return cap(p^)
}

test_raw_data :: proc(p: ^[]int) -> rawptr {
	return raw_data(p^)
}

main :: proc() {
	x := test_min_max(10, 20)
	y := test_abs(-5)
	z := test_clamp(100, 0, 50)
	_ = x + y + z

	s := []int{1, 2, 3}
	_ = test_len(&s)
	_ = test_raw_data(&s)

	d := [dynamic]int{4, 5, 6}
	_ = test_cap(&d)
}
