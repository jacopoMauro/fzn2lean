#!/usr/bin/env bash
# run.sh — upstream cross-check for the G-series semantic assumptions (W3).
#
# Each `*.mzn` here is a small ground MiniZinc model whose `output` prints the
# *evaluated* value of a MiniZinc construct corresponding to a Lean
# interpretation in `LeanFzn/Semantics/StdLib.lean` (G2 `int_div`/`int_mod`,
# G4 `int_pow`, G5 `set_le`/`set_lt`, G6 `*_nonshifted` element variants).
# `expected.txt` records, per model, the exact stdout MiniZinc 2.10.1 must
# print (or, for the undefined-boundary models, the substring its error must
# contain).  This runner passes only when every record reproduces exactly.
#
# Usage:
#   eval "$(bash audits/install_oracles.sh --print-env)"   # PATH + LD_LIBRARY_PATH
#   bash Tests/Upstream/assumptions/run.sh
#
# Oracle discovery: `minizinc` is taken from PATH, and its version must say
# 2.10.1.  The bundle's Qt/GL runtime needs `<prefix>/lib` on
# LD_LIBRARY_PATH; pass it either through the environment (as above) or as
# `LEANFZN_ORACLE_LIB=<prefix>/lib`, in which case each model runs in a
# subshell with a scoped LD_LIBRARY_PATH (the caller's shell is untouched).
# A missing or wrong-version oracle is INCOMPLETE and exits 2; a skipped check
# is never a pass.
set -u

HERE="$(cd "$(dirname "$0")" && pwd)"
MANIFEST="$HERE/expected.txt"

incomplete() { printf 'INCOMPLETE: %s\n' "$*" >&2; exit 2; }
fail() { printf 'FAIL: %s\n' "$*" >&2; exit 1; }

command -v minizinc >/dev/null 2>&1 ||
  incomplete "minizinc not on PATH (install the bundle and export PATH)"

# Run `minizinc` with the bundle runtime, scoped to this invocation.
mzn() {
  if [ -n "${LEANFZN_ORACLE_LIB:-}" ]; then
    ( LD_LIBRARY_PATH="$LEANFZN_ORACLE_LIB${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}" \
        exec minizinc "$@" )
  else
    exec minizinc "$@"
  fi
}

VERSION="$(mzn --version 2>/dev/null | head -1)"
case "$VERSION" in
  *"version 2.10.1"*) : ;;
  *) incomplete "unexpected MiniZinc version: $VERSION" ;;
esac

[ -f "$MANIFEST" ] || fail "missing manifest $MANIFEST"

# Manifest grammar (one record per model):
#   === <file> ===
#   want: stdout          # exact expected stdout, "|"-joined lines
#   want-stderr: <text>   # exact expected stderr substring, or "none"
#   --- end ---
# Empty stdout is written as the single line `(empty)`.
read_field() {  # read_field <name> <field>
  awk -v n="$1" -v f="$2" '
    $0 == "=== " n " ===" { on = 1; next }
    on && $0 == "--- end ---" { exit }
    on && index($0, f ": ") == 1 { print substr($0, length(f) + 3); exit }
  ' "$MANIFEST"
}

models="$(awk '/^=== .* ===$/ { s = $0; sub(/^=== /, "", s); sub(/ ===$/, "", s); print s }' "$MANIFEST")"
[ -n "$models" ] || fail "manifest lists no models"

status=0
checked=0
for name in $models; do
  [ -f "$HERE/$name" ] || { printf 'FAIL: manifest names missing model %s\n' "$name" >&2; status=1; continue; }
  want_out="$(read_field "$name" want)"
  want_err="$(read_field "$name" want-stderr)"
  [ -n "$want_err" ] || { printf 'FAIL: %s has no want-stderr record\n' "$name" >&2; status=1; continue; }

  err_file="$(mktemp)"
  out="$(mzn "$HERE/$name" 2>"$err_file")"
  err="$(cat "$err_file")"
  rm -f "$err_file"

  [ "$want_out" = "(empty)" ] && want_out=""
  # `run.sh` and `test_upstream_assumptions.py` compare the stdout with its
  # trailing newline removed and its lines joined by "|"; make the `$()`
  # capture above match that normal form.
  if [ -n "$out" ]; then
    out="${out//$'\n'/|}"
  fi

  ok=1
  if [ "$out" != "$want_out" ]; then
    printf 'FAIL: %s stdout\n  expected:\n%s\n  observed:\n%s\n' "$name" "$want_out" "$out" >&2
    ok=0
  fi
  if [ "$want_err" = "none" ]; then
    if [ -n "$err" ]; then
      printf 'FAIL: %s unexpected stderr:\n%s\n' "$name" "$err" >&2
      ok=0
    fi
  else
    case "$err" in
      *"$want_err"*) : ;;
      *) printf 'FAIL: %s stderr lacks %q:\n%s\n' "$name" "$want_err" "$err" >&2; ok=0 ;;
    esac
  fi
  if [ "$ok" = 1 ]; then checked=$((checked + 1)); else status=1; fi
done

[ "$status" -eq 0 ] || fail "at least one upstream case disagreed"
printf 'PASS: %d upstream assumption models reproduce expected.txt (%s)\n' \
  "$checked" "$VERSION"
