#!/bin/bash
# Compile all MiniZinc Challenge instances to FlatZinc.
#
# Backend: Gecode engine, but with the SOLVER-NEUTRAL "-G std" globals library.
# The neutral library keeps globals as standard predicates / std-lib
# decompositions instead of emitting Gecode-branded predicates
# (gecode_int_element, gecode_table_int, gecode_global_cardinality, ...)
# that the LeanFzn checker/solver does not support.  See README.md in this
# directory for the rationale.
#
# Usage: ./compile_fzn.sh [YEAR]
#   e.g. ./compile_fzn.sh 2025   or   ./compile_fzn.sh 2026   or both (default)
set -u
MZNbin="$(dirname "$0")/../../MiniZincIDE-2.10.1-x86_64-linux-gnu/bin"
[ -d "$MZNbin" ] || MZNbin="$HOME/MiniZincIDE-2.10.1-x86_64-linux-gnu/bin"
export PATH="$MZNbin:$PATH"
BASE="$(cd "$(dirname "$0")" && pwd)"
YEARS="${1:-2025 2026}"
PER_FILE_TIMEOUT=300

for Y in $YEARS; do
  INDIR="$BASE/${Y}mzn"
  OUTDIR="$BASE/${Y}fzn"
  mkdir -p "$OUTDIR"
  echo "=== $Y : compiling all instances with Gecode (-G std, neutral globals) ==="
  ok=0; failed=0
  for d in "$INDIR"/*/; do
    prob="$(basename "$d")"
    mkdir -p "$OUTDIR/$prob"
    # data files paired with the main model: compile every data file against the model
    # find the model file (first .mzn sorted) and each data file (.dzn/.json)
    mzn="$(find "$d" -maxdepth 1 -name '*.mzn' | sort | head -1)"
    [ -z "$mzn" ] && { echo "  [SKIP] $prob: no model file"; continue; }
    for data in $(find "$d" -maxdepth 1 \( -name '*.dzn' -o -name '*.json' \) | sort); do
      # strip directory and extension
      base="$(basename "$data")"
      base="${base%.*}"
      out="$OUTDIR/$prob/$base.fzn"
      if timeout "$PER_FILE_TIMEOUT" minizinc --solver Gecode -G std -c --no-output-ozn \
          -o "$out" "$mzn" "$data" > "/tmp/fzn_${prob}_${base}.log" 2>&1; then
        ok=$((ok+1))
      else
        rm -f "$out"
        failed=$((failed+1))
        echo "  [FAIL] $prob/$base : log /tmp/fzn_${prob}_${base}.log"
      fi
    done
  done
  echo "=== $Y done: $ok compiled, $failed failed ==="
done
