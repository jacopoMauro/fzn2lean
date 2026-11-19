#!/usr/bin/env bash
# audits/run_release_gates.sh — isolated PGO / non-PGO release gate (C1-C3).
#
# Usage:
#   audits/run_release_gates.sh [OUT_DIR]
#
# The default OUT_DIR is tmp/release-gates/<UTC>-<git-short-head>.  Run it
# from anywhere; it changes to the repository root itself.
#
# It performs, in order:
#   1. a fresh frozen source snapshot in tmp/release/<id>/pgo (tracked files
#      plus non-ignored untracked implementation source, the committed
#      release cohort and its fixtures; never .lake/, tmp/, .git/ or local
#      configuration);
#   2. the non-PGO selection: copy the snapshot to .../nopgo and remove
#      exactly the package `moreLeancArgs` line from nopgo/lakefile.toml;
#   3. two serial, `nice`d `lake build leanfzn` builds under one flock, each
#      with its own .lake; the developer tree's .lake is never touched;
#   4. the snapshot copy of audits/release_compare.py with the snapshot
#      audits/fixed_k.py, which writes manifest.json, comparison.json and
#      summary.txt and runs the committed release cohort.  The comparator is
#      invoked with --require-snapshot-harness so a byte-level harness
#      substitution fails setup instead of passing.
#
# The gate fails closed on every missing dependency, build failure, snapshot
# mismatch, missing fixture, unreadable binary, malformed/missing stats,
# timeout, wrong objective or rejected witness.  It never calls
# audits/run_gates.sh (C3.3) and never deletes or reuses the main .lake.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

need_cmd() {
  command -v "$1" >/dev/null 2>&1 || {
    printf 'RELEASE GATE: FAIL: required command not found: %s\n' "$1" >&2
    exit 1
  }
}

need_cmd git
need_cmd python3
need_cmd sha256sum
need_cmd timeout
need_cmd flock
need_cmd nice
need_cmd lake

# The release gate's independent evidence includes running the released binary
# against the pinned Gecode oracle, so the oracles are a required dependency.
# A missing oracle is a setup failure, never a pass; the only exception is the
# explicit LEANFZN_ALLOW_NO_ORACLE=1 downgrade, which fails as INCOMPLETE.
ORACLE_PREFIX="$ROOT/tmp/oracles/minizinc"
ORACLES_PRESENT=0
if [ -x "$ORACLE_PREFIX/bin/minizinc" ] && [ -x "$ORACLE_PREFIX/bin/fzn-gecode" ]; then
  EXPORTED_LD_LIBRARY_PATH="$ORACLE_PREFIX/lib"
  EXPORTED_PATH_PREFIX="$ORACLE_PREFIX/bin"
  ORACLES_PRESENT=1
elif command -v minizinc >/dev/null 2>&1 && command -v fzn-gecode >/dev/null 2>&1; then
  EXPORTED_LD_LIBRARY_PATH="${LD_LIBRARY_PATH:-}"
  EXPORTED_PATH_PREFIX=""
  ORACLES_PRESENT=1
fi

incomplete() {
  printf 'RELEASE GATE: INCOMPLETE: %s\n' "$*" >&2
  exit 3
}

if [ "$ORACLES_PRESENT" -ne 1 ]; then
  if [ "${LEANFZN_ALLOW_NO_ORACLE:-}" = "1" ]; then
    incomplete "oracles missing (LEANFZN_ALLOW_NO_ORACLE=1 overrides the requirement); run audits/install_oracles.sh"
  fi
  printf 'RELEASE GATE: FAIL: oracles missing: install with audits/install_oracles.sh or put minizinc and fzn-gecode on PATH\n' >&2
  exit 1
fi

STAMP="$(date -u +%Y%m%dT%H%M%SZ)"
HEAD_SHORT="$(git rev-parse --short=12 HEAD)"
RELEASE_ID="${RELEASE_ID:-${STAMP}-${HEAD_SHORT}}"
RELEASE_ROOT="${RELEASE_ROOT:-$ROOT/tmp/release}"
BUILD_ROOT="$RELEASE_ROOT/$RELEASE_ID"
PGO_DIR="$BUILD_ROOT/pgo"
NOPGO_DIR="$BUILD_ROOT/nopgo"
OUT="${1:-$ROOT/tmp/release-gates/$RELEASE_ID}"
COHORT="$ROOT/audits/release_cohort.tsv"
CAP="${RELEASE_CAP:-60}"
FIXED_K_TIMEOUT="${RELEASE_FIXED_K_TIMEOUT:-3600}"

if [ -e "$BUILD_ROOT" ]; then
  printf 'RELEASE GATE: FAIL: refusing to reuse existing snapshot %s\n' \
    "$BUILD_ROOT" >&2
  exit 1
fi
if [ ! -f "$COHORT" ]; then
  printf 'RELEASE GATE: FAIL: missing committed cohort %s\n' "$COHORT" >&2
  exit 1
fi
mkdir -p "$OUT" "$BUILD_ROOT"

trap 'rc=$?; printf "RELEASE GATE: FAIL (step failed, rc=%s)\n" "$rc" >&2; exit "$rc"' ERR

# Record the oracle provenance next to the release evidence.  fzn-gecode has no
# --version flag (`--version` is parsed as a file name and exits 1), so the
# banner printed by -help is the version record.  The same env must reach the
# snapshot comparator, which runs the oracle itself.
( export PATH="${EXPORTED_PATH_PREFIX:+$EXPORTED_PATH_PREFIX:}$PATH"
  export LD_LIBRARY_PATH="$EXPORTED_LD_LIBRARY_PATH"
  printf 'oracle-prefix: %s\n' "$ORACLE_PREFIX"
  printf 'minizinc:      %s\n' "$(command -v minizinc)"
  printf 'fzn-gecode:    %s\n' "$(command -v fzn-gecode)"
  printf 'ld-library-path: %s\n' "$EXPORTED_LD_LIBRARY_PATH"
  printf '=== minizinc --version ===\n'
  minizinc --version
  printf '=== fzn-gecode -help (first 8 lines) ===\n'
  fzn-gecode -help 2>&1 | sed -n '1,8p'
  printf '=== sha256 ===\n'
  sha256sum "$(command -v minizinc)" "$(command -v fzn-gecode)"
) >"$OUT/oracles.log" 2>&1 || {
  printf 'RELEASE GATE: FAIL: oracles are present but do not run\n' >&2
  cat "$OUT/oracles.log" >&2
  exit 1
}
if ! grep -q '^ - Version: ' "$OUT/oracles.log" \
   || grep -q 'not found\|No such file' "$OUT/oracles.log"; then
  printf 'RELEASE GATE: FAIL: oracle version probe failed (see %s)\n' \
    "$OUT/oracles.log" >&2
  exit 1
fi
printf 'oracles:     %s (%s; see %s)\n' \
  "$(sed -n 's/.*version \([^,]*\),.*/\1/p' "$OUT/oracles.log" | head -1)" \
  "$(sed -n 's/^ - Version: /gecode /p' "$OUT/oracles.log" | head -1)" \
  "$OUT/oracles.log"

printf 'release id: %s\n' "$RELEASE_ID"
printf 'snapshot:   %s\n' "$BUILD_ROOT"
printf 'out:        %s\n' "$OUT"
printf 'cohort:     %s\n' "$COHORT"

# --------------------------------------------------------------- 1. snapshot
# An allowlist, not a whole-tree copy: minizinc-challenge/ is 3.8 GB and is not
# a build input.  Everything under LeanFzn/ (tracked or non-ignored untracked)
# is included, so a dirty worktree cannot hide implementation source.
python3 - "$ROOT" "$PGO_DIR" "$COHORT" <<'PY'
from __future__ import annotations
import csv
import subprocess
import sys
from pathlib import Path

root = Path(sys.argv[1]).resolve()
dest = Path(sys.argv[2])
cohort = Path(sys.argv[3])

paths = [
    "lakefile.toml",
    "lean-toolchain",
    "lake-manifest.json",
    "Main.lean",
    "LeanFzn.lean",
    "LeanFzn",
    "pgo/default.profdata",
    "pgo/README.md",
    "audits/release_cohort.tsv",
    "audits/fixed_k.py",
    "audits/release_compare.py",
    "audits/run_release_gates.sh",
    "audits/check_semantic_inventory.py",
    "specification",
    "Tests/Semantics",
    "Tests/Audits/test_semantic_inventory.py",
    "audits/benchmark_fixtures",
    "Tests/Fixtures/Solver",
    "minizinc-wrapper/Dockerfile",
]
# Include every model named by the cohort even if it lives outside the
# directories above.  The cohort is a committed, relative-path file.
text = cohort.read_text(encoding="utf-8")
rows = [line for line in text.splitlines()
        if line.strip() and not line.lstrip().startswith("#")]
if not rows:
    raise SystemExit("release cohort has no header")
header = [h.strip() for h in next(csv.reader([rows[0]], delimiter="\t"))]
if "model" not in header:
    raise SystemExit("release cohort has no model column")
mi = header.index("model")
for row in csv.reader(rows[1:], delimiter="\t"):
    if len(row) != len(header):
        raise SystemExit("release cohort row has the wrong column count")
    model = row[mi].strip()
    if not model:
        raise SystemExit("release cohort has an empty model path")
    if Path(model).is_absolute():
        raise SystemExit(f"release cohort model must be relative: {model}")
    paths.append(model)

seen: set[str] = set()
files: list[str] = []
for path in paths:
    try:
        p = subprocess.run(
            ["git", "ls-files", "-z", "-c", "-o", "--exclude-standard",
             "--", path],
            cwd=root, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            check=True)
    except subprocess.CalledProcessError as exc:
        raise SystemExit(f"git ls-files failed for {path}: {exc.stderr!r}")
    for raw in p.stdout.split(b"\0"):
        if not raw:
            continue
        rel = raw.decode("utf-8")
        if rel in seen:
            continue
        seen.add(rel)
        files.append(rel)
if not files:
    raise SystemExit("snapshot file list is empty")

required = {
    "lakefile.toml", "lean-toolchain", "lake-manifest.json", "Main.lean",
    "pgo/default.profdata",
}
missing = sorted(required - seen)
if missing:
    raise SystemExit(f"snapshot is missing required files: {missing}")

for rel in sorted(files):
    src = root / rel
    if not src.is_file():
        raise SystemExit(f"snapshot input is not a regular file: {src}")
    dst = dest / rel
    dst.parent.mkdir(parents=True, exist_ok=True)
    dst.write_bytes(src.read_bytes())
    dst.chmod(src.stat().st_mode & 0o777)
print(f"snapshot files: {len(files)}")
PY

# Validate the frozen source and review evidence, rather than a possibly
# changing developer tree. Preserve the evidence in the release snapshot.
(cd "$PGO_DIR" && python3 -B audits/check_semantic_inventory.py --require-clean) \
  >"$OUT/semantics.log" 2>&1
printf 'semantic inventory: PASS (coverage/freshness; not an upstream equivalence proof)\n'

# ---------------------------------------------------- 2. non-PGO selection
cp -a "$PGO_DIR/." "$NOPGO_DIR/"
python3 - "$NOPGO_DIR/lakefile.toml" <<'PY'
from __future__ import annotations
import re
import sys
from pathlib import Path

path = Path(sys.argv[1])
text = path.read_text(encoding="utf-8")
lines = text.splitlines(keepends=True)
idx = [i for i, line in enumerate(lines)
       if re.match(r"^\s*moreLeancArgs\s*=", line)]
if len(idx) != 1:
    raise SystemExit(
        f"{path}: expected exactly one package moreLeancArgs line, got {len(idx)}")
if "-fprofile-use" not in lines[idx[0]]:
    raise SystemExit(f"{path}: the removed line is not the PGO selection")
del lines[idx[0]]
path.write_text("".join(lines), encoding="utf-8")
print(f"non-PGO diff: removed one moreLeancArgs line from {path}")
PY
if diff -u "$PGO_DIR/lakefile.toml" "$NOPGO_DIR/lakefile.toml" \
     >"$OUT/lakefile-nopgo.diff"; then
  printf 'RELEASE GATE: FAIL: non-PGO lakefile.toml is unchanged\n' >&2
  exit 1
fi
if [ "$(grep -c '^-moreLeancArgs' "$OUT/lakefile-nopgo.diff" || true)" -ne 1 ]; then
  printf 'RELEASE GATE: FAIL: non-PGO diff is not exactly one moreLeancArgs line\n' >&2
  exit 1
fi

# --------------------------------------------------------------- 3. builds
mkdir -p "$ROOT/tmp"
exec 9>"$ROOT/tmp/lake.lock"
if ! flock -n 9; then
  printf 'RELEASE GATE: FAIL: another build holds %s\n' "$ROOT/tmp/lake.lock" >&2
  exit 1
fi
build_variant() {
  local dir="$1" log="$2"
  printf 'building %s\n' "$dir"
  ( cd "$dir" && nice -n 10 lake build leanfzn ) >"$log" 2>&1
}
build_variant "$PGO_DIR" "$OUT/build-pgo.log"
build_variant "$NOPGO_DIR" "$OUT/build-nopgo.log"
exec 9>&-

PGO_BIN="$PGO_DIR/.lake/build/bin/leanfzn"
NOPGO_BIN="$NOPGO_DIR/.lake/build/bin/leanfzn"
for bin in "$PGO_BIN" "$NOPGO_BIN"; do
  if [ ! -x "$bin" ]; then
    printf 'RELEASE GATE: FAIL: build did not produce executable %s\n' "$bin" >&2
    exit 1
  fi
done
PGO_LAKE="$(readlink -f "$PGO_DIR/.lake")"
NOPGO_LAKE="$(readlink -f "$NOPGO_DIR/.lake")"
MAIN_LAKE="$(readlink -f "$ROOT/.lake")"
if [ "$PGO_LAKE" = "$MAIN_LAKE" ] || [ "$NOPGO_LAKE" = "$MAIN_LAKE" ] \
   || [ "$PGO_LAKE" = "$NOPGO_LAKE" ]; then
  printf 'RELEASE GATE: FAIL: build trees are not isolated\n' >&2
  exit 1
fi
PGO_SHA="$(sha256sum "$PGO_BIN" | cut -d' ' -f1)"
NOPGO_SHA="$(sha256sum "$NOPGO_BIN" | cut -d' ' -f1)"
if [ "$PGO_SHA" = "$NOPGO_SHA" ]; then
  printf 'RELEASE GATE: FAIL: PGO and non-PGO binaries are identical\n' >&2
  exit 1
fi
printf 'pgo binary:   %s %s\n' "$PGO_BIN" "$PGO_SHA"
printf 'nopgo binary: %s %s\n' "$NOPGO_BIN" "$NOPGO_SHA"

# ----------------------------------------------------------- 4. comparison
# Run the harness from the snapshot, not from the developer tree, and pass
# --require-snapshot-harness so release_compare.py rejects any byte-level
# harness substitution.  --git-root points provenance at the real repository
# while the comparator itself lives in a snapshot without .git.
SNAPSHOT_COMPARE="$PGO_DIR/audits/release_compare.py"
SNAPSHOT_FIXED_K="$PGO_DIR/audits/fixed_k.py"
for fixture in "$SNAPSHOT_COMPARE" "$SNAPSHOT_FIXED_K"; do
  if [ ! -f "$fixture" ]; then
    printf 'RELEASE GATE: FAIL: snapshot harness missing %s\n' "$fixture" >&2
    exit 1
  fi
done
COMPARE_SHA="$(sha256sum "$SNAPSHOT_COMPARE" | cut -d' ' -f1)"
FIXED_K_SHA="$(sha256sum "$SNAPSHOT_FIXED_K" | cut -d' ' -f1)"
printf 'comparator:  %s %s\n' "$SNAPSHOT_COMPARE" "$COMPARE_SHA"
printf 'fixed-k:     %s %s\n' "$SNAPSHOT_FIXED_K" "$FIXED_K_SHA"

status=0
extra_args=()
if [ -n "${RELEASE_MEASURE_LOCK:-}" ]; then
  extra_args=(--measure-lock "$RELEASE_MEASURE_LOCK")
fi
RELEASE_ID="$RELEASE_ID" \
PATH="${EXPORTED_PATH_PREFIX:+$EXPORTED_PATH_PREFIX:}$PATH" \
LD_LIBRARY_PATH="$EXPORTED_LD_LIBRARY_PATH" \
python3 -B "$SNAPSHOT_COMPARE" \
  --pgo-binary "$PGO_BIN" \
  --nopgo-binary "$NOPGO_BIN" \
  --snapshot-pgo "$PGO_DIR" \
  --snapshot-nopgo "$NOPGO_DIR" \
  --cohort "$COHORT" \
  --cap "$CAP" \
  --fixed-k-timeout "$FIXED_K_TIMEOUT" \
  --fixed-k "$SNAPSHOT_FIXED_K" \
  --require-snapshot-harness \
  --require-oracle \
  --git-root "$ROOT" \
  --out "$OUT" \
  "${extra_args[@]}" \
  || status=$?

if [ "$status" -eq 0 ]; then
  printf 'RELEASE GATE: PASS\n'
else
  printf 'RELEASE GATE: FAIL (release_compare rc=%s)\n' "$status" >&2
fi
exit "$status"
