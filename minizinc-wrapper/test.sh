#!/usr/bin/env bash
# Smoke test of the MiniZinc integration. Uses a temporary copy of the in-tree
# leanfzn.msc with absolute paths (MiniZinc 2.10 does not resolve a relative
# "executable"), so it does not need install.sh. Every solution found is re-checked by
# `leanfzn check` against the FlatZinc MiniZinc produced.
#   ./test.sh [path/to/minizinc]
set -uo pipefail
MZN="${1:-minizinc}"
DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LEANFZN="${LEANFZN_BIN:-$DIR/../.lake/build/bin/leanfzn}"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
MSC="$TMP/leanfzn.msc"
python3 - "$DIR" "$MSC" <<'PY'
import json, os, sys
d, target = sys.argv[1], sys.argv[2]
msc = json.load(open(os.path.join(d, "leanfzn.msc")))
msc["executable"] = os.path.join(d, msc["executable"])
msc["mznlib"] = os.path.join(d, msc["mznlib"])
json.dump(msc, open(target, "w"), indent=2)
PY
fail=0

echo "minizinc: $("$MZN" --version | head -1)"

# run NAME EXPECTED-REGEX [extra minizinc args...]
run() {
  local name="$1" want="$2"; shift 2
  local out
  out="$("$MZN" --solver "$MSC" "$DIR/examples/$name.mzn" "$@" 2>&1)"
  local code=$?
  if [ "$code" -eq 0 ] && grep -qE "$want" <<<"$out"; then
    echo "PASS  $name $*"
  else
    echo "FAIL  $name $*  (expected /$want/)"; echo "$out" | tail -5 | sed 's/^/      /'
    fail=1
  fi
}

run queens   '^q = \['
run packing  'value = 51'
run packing  '^==========$'
run unsat    '=====UNSATISFIABLE====='
run float    'UNSUPPORTED|UNKNOWN'
run golomb   'length = [0-9]+' -t 3000
run packing  '%%%mzn-stat: failures=' -s

# Independent check: solve the flattened model directly and verify every
# emitted solution with the verified checker.
for name in queens packing; do
  if "$MZN" -c --solver "$MSC" "$DIR/examples/$name.mzn" --fzn "$TMP/$name.fzn" --ozn "$TMP/$name.ozn" >/dev/null 2>&1 \
     && "$LEANFZN" solve "$TMP/$name.fzn" > "$TMP/$name.sol" 2>/dev/null \
     && grep -qx -- '----------' "$TMP/$name.sol" \
     && "$LEANFZN" check "$TMP/$name.fzn" "$TMP/$name.sol" >/dev/null 2>&1; then
    echo "PASS  check $name"
  else
    echo "FAIL  check $name"; fail=1
  fi
done

[ "$fail" = 0 ] && echo "all tests passed" || echo "some tests FAILED"
exit "$fail"
