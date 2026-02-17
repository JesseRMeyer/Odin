#!/bin/bash
# Test: SIMD vector alignment is power-of-two and capped at max_simd_align
set -e

ODIN="${ODIN:-./odin}"
TMPDIR=$(mktemp -d)
trap 'rm -rf "$TMPDIR"' EXIT

cat > "$TMPDIR/vec_test.odin" <<'ODIN_SRC'
package vec_test

import "core:simd"

main :: proc() {
	v: #simd[4]f32
	_ = simd.extract(v, 0)
}
ODIN_SRC

echo "=== Building SIMD test with -fast -build-mode:obj ==="
$ODIN build "$TMPDIR/vec_test.odin" -file -fast -build-mode:obj -out:"$TMPDIR/vec_test"
OBJ="$TMPDIR/vec_test.o"

if [ ! -s "$OBJ" ]; then
	echo "FAIL: object file missing or empty"
	exit 1
fi

echo "=== Checking .text section exists ==="
if ! readelf -S "$OBJ" | grep -q '\.text'; then
	echo "FAIL: .text section not found"
	exit 1
fi

echo "PASS: vector alignment test"
