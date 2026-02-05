package test_comp_simple

import "core:fmt"

compute_magic :: proc() -> i32 {
	return 42
}

main :: proc() {
	x := #comp compute_magic()
	fmt.println(x)
}
