#!/bin/bash
# Test: -fast works on Linux x86-64 and rejects unsupported targets
set -e

ODIN="${ODIN:-./odin}"
TMPDIR=$(mktemp -d)
trap 'rm -rf "$TMPDIR"' EXIT

cat > "$TMPDIR/gate_test.odin" <<'ODIN_SRC'
package gate_test

main :: proc() {}
ODIN_SRC

echo "=== Test 1: -fast on native Linux x86-64 ==="
$ODIN build "$TMPDIR/gate_test.odin" -file -fast -build-mode:obj -out:"$TMPDIR/gate_test"
if [ ! -s "$TMPDIR/gate_test.o" ]; then
	echo "FAIL: object file not created on native target"
	exit 1
fi
echo "PASS: native target accepted"

echo "=== Test 2: -fast with -target:linux_arm64 should fail ==="
if $ODIN build "$TMPDIR/gate_test.odin" -file -fast -build-mode:obj -target:linux_arm64 -out:"$TMPDIR/gate_arm" 2>/dev/null; then
	echo "FAIL: cross-compile to arm64 should have been rejected"
	exit 1
fi
echo "PASS: unsupported target rejected"
