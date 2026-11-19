#!/usr/bin/env bash
# audits/check_native_seams.sh — mechanically check every native substitution.
#
# W7: no compiled replacement may depend on an unchecked attribute.  This
# script has two halves:
#
#   1. the Python scanner (`audits/native_seams_scan.py`) parses the tree for
#      every `@[implemented_by]` / `attribute [implemented_by]` and
#      `@[csimp]` / `attribute [csimp]` seam, blanking comments first — so an
#      attribute in a comment or docstring does not count and an attribute in
#      code cannot hide;
#   2. the Lean metaprogram (`audits/NativeSeams.lean`) enumerates the
#      `implemented_by` pairs from the environment and validates the
#      inventory `audits/native_seams.json`: every seam has exactly one entry,
#      every entry's theorem exists and its elaborated type is
#      `∀ …, ref … = impl …` (or a guarded form with a named carrier).
#
# Both halves must agree on the `csimp` rows: the inventory's `thm` for a
# `csimp` seam is the source-level theorem the attribute names, and the Lean
# side re-checks the kernel statement.
#
# Usage:
#   bash audits/check_native_seams.sh                 # check the repository
#   bash audits/check_native_seams.sh --self-test     # must FAIL (broken copy)
#   bash audits/check_native_seams.sh --print-inventory
#
# Exit status: 0 when every seam is covered by a kernel-checked theorem, 1
# otherwise.  `--self-test` inverts the verdict: it copies the tree, breaks one
# inventory entry, and succeeds only when the audit rejects the copy.
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT" || exit 1
MODE="${1:-}"


if [ "$MODE" = "--print-inventory" ]; then
  python3 "$ROOT/audits/native_seams_scan.py" all
  exit $?
fi

if [ "$MODE" = "--self-test" ]; then
  TMP="$(mktemp -d)"
  trap 'rm -rf "$TMP"' EXIT
  # A copy of the repository's audit inputs with one broken entry.
  mkdir -p "$TMP/audits"
  cp "$ROOT/audits/NativeSeams.lean" "$TMP/audits/"
  cp "$ROOT/audits/native_seams_scan.py" "$TMP/audits/"
  python3 - "$ROOT/audits/native_seams.json" "$TMP/audits/native_seams.json" <<'PY'
import json, sys
data = json.load(open(sys.argv[1], encoding="utf-8"))
target = next(e for e in data["seams"] if e["kind"] == "impl_by")
target["impl"] = target["impl"] + "_not_the_real_target"
json.dump(data, open(sys.argv[2], "w", encoding="utf-8"), indent=1)
PY
  # The audit imports `LeanFzn` and reads the inventory from the root it is
  # given; run it against the broken copy.
  if lake env lean --run "$ROOT/audits/NativeSeams.lean" -- "$TMP" \
       >"$TMP/out.log" 2>&1; then
    echo "SELF-TEST FAILED: the broken inventory was accepted" >&2
    cat "$TMP/out.log" >&2
    exit 1
  fi
  if ! grep -q '^FAIL ' "$TMP/out.log"; then
    echo "SELF-TEST FAILED: the audit failed without a FAIL line" >&2
    cat "$TMP/out.log" >&2
    exit 1
  fi
  echo "SELF-TEST OK: the broken inventory was rejected"
  exit 0
fi

fail=0

# 1. The scanner must find every attribute the Lean environment reports.
echo "native-seams: scanning the tree"
python3 "$ROOT/audits/native_seams_scan.py" all 2>/dev/null >"$ROOT/tmp/native_seams_scan.tsv"
scan_rc=$?
if [ $scan_rc -ne 0 ]; then
  echo "FAIL: audits/native_seams_scan.py exited $scan_rc" >&2
  exit 1
fi
scan_count=$(grep -c . "$ROOT/tmp/native_seams_scan.tsv" || true)
echo "native-seams: $scan_count seams in the tree"

# 2. The scanner's self-check: every `#check` of an inventory theorem must
#    resolve, so a renamed or deleted seam theorem fails after a build.
python3 - "$ROOT" <<'PY' >"$ROOT/tmp/native_seams_check.lean"
import json, sys
root = sys.argv[1]
data = json.load(open(root + "/audits/native_seams.json", encoding="utf-8"))
print("import LeanFzn")
for e in data["seams"]:
    print(f"#check {e['thm']}")
PY
if ! lake env lean "$ROOT/tmp/native_seams_check.lean" >"$ROOT/tmp/native_seams_check.log" 2>&1; then
  echo "FAIL: a seam theorem named in audits/native_seams.json does not check:" >&2
  grep -E 'error' "$ROOT/tmp/native_seams_check.log" | head -20 >&2
  fail=1
fi

# 3. The Lean audit: environment coverage, inventory agreement, theorem shape.
if lake env lean --run "$ROOT/audits/NativeSeams.lean" -- "$ROOT" \
     >"$ROOT/tmp/native_seams.log" 2>&1; then
  tail -2 "$ROOT/tmp/native_seams.log"
else
  echo "FAIL: audits/NativeSeams.lean rejected the inventory:" >&2
  grep -E '^FAIL ' "$ROOT/tmp/native_seams.log" | head -30 >&2
  fail=1
fi

if [ $fail -eq 0 ]; then
  echo "native-seams check PASSED"
  exit 0
fi
echo "native-seams check FAILED"
exit 1
