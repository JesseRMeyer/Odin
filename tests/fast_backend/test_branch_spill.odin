package test_branch_spill

// Minimal test: two consecutive if-checks.
// This crashes with the block-boundary spill bug because
// the second if's block starts with spill code shaped for
// the first if's block, not for the entry block.

foreign import libc "system:c"
foreign libc {
	exit :: proc "c" (code: i32) ---
}

main :: proc() {
	a : int = 3 + 4
	if a != 7 {
		exit(1)
	}
	b : int = a * 2
	if b != 14 {
		exit(2)
	}
	exit(0)
}
