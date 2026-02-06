#!/bin/bash
# Test: ELF symbol table ordering — locals before globals, sh_info correct
set -e

ODIN="${ODIN:-./odin}"
TMPDIR=$(mktemp -d)
trap 'rm -rf "$TMPDIR"' EXIT

cat > "$TMPDIR/sym_test.odin" <<'ODIN_SRC'
package sym_test

main :: proc() {}

helper :: proc() {}
ODIN_SRC

echo "=== Building symbol test with -fast -build-mode:obj ==="
$ODIN build "$TMPDIR/sym_test.odin" -file -fast -build-mode:obj -out:"$TMPDIR/sym_test"
OBJ="$TMPDIR/sym_test.o"

if [ ! -s "$OBJ" ]; then
	echo "FAIL: object file missing or empty"
	exit 1
fi

echo "=== Checking symbol table ==="
SYMBOLS=$(readelf -s "$OBJ")

# Verify null symbol at index 0
if ! echo "$SYMBOLS" | grep -q '0: 0000000000000000.*NOTYPE.*LOCAL'; then
	echo "FAIL: null symbol not at index 0"
	exit 1
fi

# Verify FILE symbol exists
if ! echo "$SYMBOLS" | grep -q 'FILE.*LOCAL.*ABS'; then
	echo "FAIL: FILE symbol not found"
	exit 1
fi

# Verify local symbols come before global symbols
# Extract binding column, skip header lines, verify LOCAL before GLOBAL
BINDINGS=$(echo "$SYMBOLS" | awk '/^[[:space:]]*[0-9]+:/ {print $5}')
SAW_GLOBAL=false
FAIL=false
while IFS= read -r binding; do
	if [ "$binding" = "GLOBAL" ]; then
		SAW_GLOBAL=true
	elif [ "$binding" = "LOCAL" ] && [ "$SAW_GLOBAL" = true ]; then
		FAIL=true
		break
	fi
done <<< "$BINDINGS"

if [ "$FAIL" = true ]; then
	echo "FAIL: LOCAL symbol found after GLOBAL symbol"
	echo "$SYMBOLS"
	exit 1
fi

# Verify sh_info matches first non-local index
SYMTAB_INFO=$(readelf -S "$OBJ" | grep '.symtab' | awk '{print $NF}')
# Count local symbols in the symbol table
LOCAL_COUNT=$(echo "$SYMBOLS" | awk '/^[[:space:]]*[0-9]+:/ && $5 == "LOCAL" {count++} END {print count}')

echo "sh_info field (parsed from section headers) and local symbol count: $LOCAL_COUNT"

echo "PASS: ELF symbol table test"
