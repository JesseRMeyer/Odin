package test_internal

import "core:testing"

@(private = "file")
Big :: struct {
	a, b, c, d: [4]u64,
}

@(private = "file")
make_big :: proc(seed: u64) -> Big {
	return Big{
		a = {seed, seed + 1, seed + 2, seed + 3},
		b = {seed + 4, seed + 5, seed + 6, seed + 7},
		c = {seed + 8, seed + 9, seed + 10, seed + 11},
		d = {seed + 12, seed + 13, seed + 14, seed + 15},
	}
}

@(private = "file")
validate_big :: proc(b: Big, seed: u64) -> bool {
	for i in 0 ..< 4 {
		if b.a[i] != seed + u64(i) { return false }
		if b.b[i] != seed + u64(i + 4) { return false }
		if b.c[i] != seed + u64(i + 8) { return false }
		if b.d[i] != seed + u64(i + 12) { return false }
	}
	return true
}

// Extended RVO pattern: x := call(); validate(x); return x
@(private = "file")
extended_rvo_basic :: proc(seed: u64) -> Big {
	x := make_big(seed)
	assert(validate_big(x, seed))
	return x
}

// Minimal pattern: x := call(); return x
@(private = "file")
extended_rvo_minimal :: proc(seed: u64) -> Big {
	x := make_big(seed)
	return x
}

// Multiple intervening statements
@(private = "file")
extended_rvo_multi_stmt :: proc(seed: u64) -> Big {
	x := make_big(seed)
	assert(validate_big(x, seed))
	_ = seed * 2
	return x
}

// Should NOT trigger extended RVO: control flow between decl and return
@(private = "file")
no_rvo_control_flow :: proc(seed: u64, flag: bool) -> Big {
	x := make_big(seed)
	if flag {
		assert(validate_big(x, seed))
	}
	return x
}

// Should NOT trigger extended RVO: x is reassigned
@(private = "file")
no_rvo_reassign :: proc(seed: u64) -> Big {
	x := make_big(seed)
	x = make_big(seed + 100)
	return x
}

@(test)
test_sret_rvo_basic :: proc(t: ^testing.T) {
	b := extended_rvo_basic(42)
	testing.expect(t, validate_big(b, 42), "extended RVO basic failed")
}

@(test)
test_sret_rvo_minimal :: proc(t: ^testing.T) {
	b := extended_rvo_minimal(7)
	testing.expect(t, validate_big(b, 7), "extended RVO minimal failed")
}

@(test)
test_sret_rvo_multi_stmt :: proc(t: ^testing.T) {
	b := extended_rvo_multi_stmt(99)
	testing.expect(t, validate_big(b, 99), "extended RVO multi stmt failed")
}

@(test)
test_no_rvo_control_flow :: proc(t: ^testing.T) {
	b := no_rvo_control_flow(55, true)
	testing.expect(t, validate_big(b, 55), "no RVO control flow failed")
	b2 := no_rvo_control_flow(55, false)
	testing.expect(t, validate_big(b2, 55), "no RVO control flow (false) failed")
}

@(test)
test_no_rvo_reassign :: proc(t: ^testing.T) {
	b := no_rvo_reassign(10)
	testing.expect(t, validate_big(b, 110), "no RVO reassign failed")
}
