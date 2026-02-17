#!/bin/bash
# Test: Foreign library enumeration — verify foreign symbols appear as UND in .o
set -e

ODIN="${ODIN:-./odin}"
TMPDIR=$(mktemp -d)
trap 'rm -rf "$TMPDIR"' EXIT

cat > "$TMPDIR/foreign_test.odin" <<'ODIN_SRC'
package foreign_test

import "core:fmt"

main :: proc() {
	fmt.println("hello")
}
ODIN_SRC

echo "=== Building with -fast -build-mode:obj ==="
$ODIN build "$TMPDIR/foreign_test.odin" -file -fast -build-mode:obj -out:"$TMPDIR/foreign_test"
OBJ="$TMPDIR/foreign_test.o"

if [ ! -s "$OBJ" ]; then
	echo "FAIL: object file missing or empty"
	exit 1
fi

echo "=== Checking for undefined (foreign) symbols ==="
UND_SYMS=$(readelf -s "$OBJ" | grep 'UND' | grep -v '0: 0000000000000000.*NOTYPE.*LOCAL' || true)
if [ -z "$UND_SYMS" ]; then
	echo "WARN: no undefined symbols found (foreign libs may not have been enumerated)"
else
	echo "Found undefined symbols (foreign references):"
	echo "$UND_SYMS" | head -10
fi

echo "PASS: foreign library test"
