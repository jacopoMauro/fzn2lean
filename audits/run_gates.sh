#!/usr/bin/env bash
# audits/run_gates.sh — public Core acceptance gate.
#
# Usage: audits/run_gates.sh [LOG_DIR]
#
# Runs the library/test and native executable builds, semantic inventory,
# proof/import audits, native/Python regressions, public quick suite, witness
# oracles and optional independent Gecode coverage fuzz.
# Prints one summary line per gate and exits non-zero if any fails.
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT" || exit 1
LOG="${1:-tmp/gates/$(date -u +%Y%m%dT%H%M%SZ)}"
mkdir -p "$LOG"

fail=0
incomplete=0
summary() { printf 'GATE %s\n' "$*"; }
failing() { fail=1; summary "$*: FAIL"; }

# --------------------------------------------------- 0. independent oracles
# The oracle section below is evidence only if the oracles actually run, so a
# missing oracle is a failed gate, not a skip.  The oracles are the pinned
# MiniZinc 2.10.1 bundle in tmp/oracles/ (audits/install_oracles.sh) or an
# equivalent install the caller put on PATH.  LEANFZN_ALLOW_NO_ORACLE=1
# records INCOMPLETE and continues; the exit status is still non-zero because
# the gate's completion condition was not met.
ORACLE_PREFIX="$ROOT/tmp/oracles/minizinc"
oracle_log="$LOG/oracles.log"
oracle_status="missing"
if [ -x "$ORACLE_PREFIX/bin/minizinc" ] && [ -x "$ORACLE_PREFIX/bin/fzn-gecode" ]; then
  # The bundle ships stub copies of glibc-adjacent libraries (libselinux.so.1
  # and friends) in `lib/`; putting them on the gate's own LD_LIBRARY_PATH
  # breaks unrelated tools (sed, git, python extension modules).  So the
  # oracle's runtime path is exported as `LEANFZN_ORACLE_LIB` and only the
  # oracle invocations below prepend it to their own LD_LIBRARY_PATH.
  export PATH="$ORACLE_PREFIX/bin:$PATH"
  export LEANFZN_ORACLE_LIB="$ORACLE_PREFIX/lib"
  oracle_status="installed"
elif command -v minizinc >/dev/null 2>&1 && command -v fzn-gecode >/dev/null 2>&1; then
  oracle_status="path"
fi
# The oracle runtime prefix for the oracle child processes only (`:` when the
# caller supplied the oracles and no bundle is installed).
oracle_lib="${LEANFZN_ORACLE_LIB:-}"

# Run an oracle command with the bundle's runtime library path, without
# leaking it into the gate's own environment.
with_oracle_lib() {
  if [ -n "$oracle_lib" ]; then
    env LD_LIBRARY_PATH="$oracle_lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}" "$@"
  else
    "$@"
  fi
}

record_oracle() {
  {
    printf 'oracle source: %s\n' "$*"
    printf 'minizinc path: %s\n' "$(command -v minizinc || echo '(none)')"
    printf 'fzn-gecode path: %s\n' "$(command -v fzn-gecode || echo '(none)')"
    printf '=== minizinc --version ===\n'
    with_oracle_lib minizinc --version 2>&1 || printf '(minizinc --version failed, rc=%s)\n' "$?"
    printf '=== minizinc --solvers (gecode lines) ===\n'
    with_oracle_lib minizinc --solvers 2>&1 | grep -i gecode || printf '(no Gecode solver)\n'
    # fzn-gecode has no --version flag: `--version` is parsed as a file name
    # and exits 1, so the banner from -help is the version record.
    printf '=== fzn-gecode -help (banner) ===\n'
    with_oracle_lib fzn-gecode -help 2>&1 | sed -n '1,8p' || printf '(fzn-gecode -help failed)\n'
    printf '=== sha256 of oracle binaries ===\n'
    sha256sum "$(command -v minizinc)" "$(command -v fzn-gecode)" 2>&1 \
      || printf '(sha256sum failed)\n'
  } >"$oracle_log" 2>&1
}

oracle_version_line() {
  local mzn gec
  mzn="$(with_oracle_lib minizinc --version 2>/dev/null | sed -n '1s/.*version \([^,]*\),.*/\1/p')"
  # fzn-gecode prints its banner on stderr, so 2>/dev/null would hide it.
  gec="$(with_oracle_lib fzn-gecode -help 2>&1 | sed -n 's/^ - Version: //p' | head -1)"
  printf 'minizinc %s, gecode %s' "${mzn:-unknown}" "${gec:-unknown}"
}

if [ "$oracle_status" = "missing" ]; then
  missing_text="oracles missing (run audits/install_oracles.sh; see $oracle_log)"
  : >"$oracle_log"
  if [ "${LEANFZN_ALLOW_NO_ORACLE:-}" = "1" ]; then
    incomplete=1
    summary "oracles: INCOMPLETE ($missing_text)"
  else
    failing "$missing_text"
  fi
elif record_oracle "$oracle_status" && \
     grep -q '^ - Version: ' "$oracle_log" && \
     ! grep -q 'not found\|No such file' "$oracle_log"; then
  summary "oracles: PASS ($(oracle_version_line); source=$oracle_status; see $oracle_log)"
else
  failing "oracles (not runnable; see $oracle_log)"
fi

# ---------------------------------------------------------------- 1. build
if lake build LeanFzn Tests leanfzn >"$LOG/build.log" 2>&1; then
  built=$(grep -c '^✔' "$LOG/build.log" 2>/dev/null || true)
  summary "build: PASS (${built:-0} fresh targets)"
else
  failing "build (see $LOG/build.log)"
  exit 1  # Never validate stale artifacts after the source build failed.
fi

# A passing build does not establish that the reviewed semantics are current.
if python3 -B audits/check_semantic_inventory.py --require-clean >"$LOG/semantics.log" 2>&1; then
  summary "semantic-inventory: PASS (coverage/freshness; not an upstream equivalence proof)"
else
  failing "semantic-inventory (see $LOG/semantics.log)"
  exit 1
fi

# -------------------------------------------------------- 2. executables
mapfile -t EXES < <(python3 - <<'PY'
import re
s = open('lakefile.toml').read()
print('\n'.join(re.findall(r'\[\[lean_exe\]\]\s*\nname = "([^"]+)"', s)))
PY
)
exe_pass=0; exe_fail=0; exe_skip=0
for exe in "${EXES[@]}"; do
  case "$exe" in
    challenge_scan)  # file/arg-driven measurement tools
      exe_skip=$((exe_skip+1)); summary "exe $exe: SKIP (arg-driven)"; continue ;;
    leanfzn)  # exercised by the quick suite; build it, do not run it bare
      lake build leanfzn >"$LOG/build_$exe.log" 2>&1 || failing "exe-build $exe"
      exe_skip=$((exe_skip+1)); continue ;;
  esac
  if ! lake build "$exe" >"$LOG/build_$exe.log" 2>&1; then
    exe_fail=$((exe_fail+1)); failing "exe-build $exe (see $LOG/build_$exe.log)"; continue
  fi
  timeout 300 ".lake/build/bin/$exe" >"$LOG/exe_$exe.out" 2>&1
  code=$?
  if [ $code -eq 0 ]; then exe_pass=$((exe_pass+1));
  else exe_fail=$((exe_fail+1)); fail=1; summary "exe $exe: FAIL(rc=$code, $LOG/exe_$exe.out)"; fi
done
if [ $exe_fail -eq 0 ]; then
  summary "executables: PASS ($exe_pass run, $exe_skip skipped)"
else
  summary "executables: FAIL ($exe_pass pass, $exe_fail fail)"
fi

# ------------------------------------------------------- 4. audits
if bash audits/run_axiom_audit.sh >"$LOG/axiom.log" 2>&1; then
  summary "axiom-audit: PASS ($(tail -1 "$LOG/axiom.log"))"
else
  failing "axiom-audit (see $LOG/axiom.log)"
fi

if python3 audits/check_module_boundaries.py >"$LOG/boundaries.log" 2>&1; then
  summary "boundaries: PASS ($(tail -1 "$LOG/boundaries.log"))"
else
  failing "boundaries (see $LOG/boundaries.log)"
fi

# P0: a raw `Model` may not reach a verdict except through `gate`.
if python3 audits/check_gate_usage.py >"$LOG/gate-usage.log" 2>&1; then
  summary "gate-usage: PASS ($(tail -1 "$LOG/gate-usage.log"))"
else
  failing "gate-usage (see $LOG/gate-usage.log)"
fi

# W7: every native substitution is covered by a kernel-checked seam theorem,
# and the audit has teeth (its self-test must reject a broken inventory).
if bash audits/check_native_seams.sh >"$LOG/native-seams.log" 2>&1; then
  summary "native-seams: PASS ($(tail -1 "$LOG/native-seams.log"))"
else
  failing "native-seams (see $LOG/native-seams.log)"
fi
if bash audits/check_native_seams.sh --self-test >"$LOG/native-seams-selftest.log" 2>&1; then
  summary "native-seams-self-test: PASS"
else
  failing "native-seams-self-test (see $LOG/native-seams-selftest.log)"
fi

# Public CLI behavior, import-scanner and benchmark-outcome regressions.
if python3 -B Tests/Cli/test_admission.py >"$LOG/admission.log" 2>&1; then
  summary "admission: PASS"
else
  failing "admission (see $LOG/admission.log)"
fi
if python3 -B Tests/Cli/test_solve.py >"$LOG/core-only-cli.log" 2>&1; then
  summary "core-only-cli: PASS"
else
  failing "core-only-cli (see $LOG/core-only-cli.log)"
fi
if python3 -B Tests/Cli/test_protocol.py >"$LOG/jsonl-protocol.log" 2>&1; then
  summary "jsonl-protocol: PASS"
else
  failing "jsonl-protocol (see $LOG/jsonl-protocol.log)"
fi
if python3 -B Tests/Cli/test_check_separators.py >"$LOG/check-separators.log" 2>&1; then
  summary "check-separators: PASS"
else
  failing "check-separators (see $LOG/check-separators.log)"
fi
if python3 -B -m unittest discover -s Tests/Architecture >"$LOG/import-scanner.log" 2>&1; then
  summary "import-scanner: PASS"
else
  failing "import-scanner (see $LOG/import-scanner.log)"
fi
if python3 -B -m unittest discover -s Tests/Audits >"$LOG/benchmark-outcomes.log" 2>&1; then
  summary "benchmark-outcomes: PASS"
else
  failing "benchmark-outcomes (see $LOG/benchmark-outcomes.log)"
fi

# ------------------------------------------------------------ 6. quick suite
rm -rf "$LOG/quick"
if python3 audits/benchmark_performance.py --tier quick --suite-budget 60 \
     --output "$LOG/quick" >"$LOG/quick.log" 2>&1 \
   && python3 - "$LOG/quick/results.json" >"$LOG/quick.summary" 2>&1 <<'PY'
import json, sys
r = json.load(open(sys.argv[1]))['summary']
ok = r['cases_run'] > 0 and r['skipped'] == 0 \
     and r['complete'] + r['allowed_incomplete'] == r['cases_run'] \
     and r['contract_agreement'] == r['cases_run'] \
     and r['witnesses_accepted'] == r['witness_checks']
print(f"cases={r['cases_run']} complete={r['complete']} "
      f"allowed_incomplete={r['allowed_incomplete']} "
      f"proved_agree={r['expected_agreement']} contract_agree={r['contract_agreement']} "
      f"rss={r['max_peak_rss_kib']}KiB "
      f"witnesses={r['witnesses_accepted']}/{r['witness_checks']}")
sys.exit(0 if ok else 1)
PY
then
  summary "quick-suite: PASS ($(cat "$LOG/quick.summary"))"
else
  failing "quick-suite (see $LOG/quick.log)"
fi

# ------------------------------------------------- 7. O3 oracle tools
# oracle_check.py runs over an existing strategy_matrix results directory.  By
# default the gate generates a two-model micro directory (one UNSAT, one SAT
# witness); set ORACLE_RESULTS to check a larger run instead.
if [ -n "${ORACLE_RESULTS:-}" ]; then
  oracle_dir="$ORACLE_RESULTS"
else
  oracle_dir="$LOG/oracle-check-results"
  rm -rf "$oracle_dir"
  cat >"$LOG/oracle-check-cohort.txt" <<'EOF'
audits/benchmark_fixtures/int_ne_unsat.fzn
audits/benchmark_fixtures/generated/latin3.fzn
EOF
  if ! python3 audits/strategy_matrix.py --configs default \
       --cohort "$LOG/oracle-check-cohort.txt" --cap 10 --out "$oracle_dir" \
       >"$LOG/oracle-check-run.log" 2>&1; then
    failing "oracle-check setup (see $LOG/oracle-check-run.log)"
  fi
fi
if [ -f "$oracle_dir/matrix.tsv" ]; then
  if python3 audits/oracle_check.py "$oracle_dir" \
       --binary .lake/build/bin/leanfzn --json "$LOG/oracle-check.report.json" \
       >"$LOG/oracle-check.log" 2>&1; then
    summary "oracle-check: PASS ($(grep -m1 '^witness:' "$LOG/oracle-check.log"))"
  else
    failing "oracle-check (see $LOG/oracle-check.log)"
  fi
else
  failing "oracle-check (no matrix.tsv in ${oracle_dir})"
fi

# coverage_fuzz.py compares micro-models against fzn-gecode.  Gecode is a
# development oracle only, but a missing oracle is never a silent pass: the
# fuzzer prints SKIP and this gate fails (or records INCOMPLETE under
# LEANFZN_ALLOW_NO_ORACLE=1).  --require-oracle makes the fuzzer itself
# refuse to run without Gecode.
if python3 -B audits/coverage_fuzz.py --require-oracle \
     --seeds "${O3_FUZZ_SEEDS:-200}" --start 0 \
     --binary .lake/build/bin/leanfzn --out "$LOG/coverage-fuzz" \
     >"$LOG/coverage-fuzz.log" 2>&1; then
  if grep -q '^FUZZ FAMILIES-MISSING none$' "$LOG/coverage-fuzz.log"; then
    summary "coverage-fuzz: PASS ($(grep -m1 '^FUZZ SUMMARY' "$LOG/coverage-fuzz.log"))"
  else
    failing "coverage-fuzz did not cover every generator family ($(grep -m1 '^FUZZ FAMILIES-MISSING' "$LOG/coverage-fuzz.log"); see $LOG/coverage-fuzz.log)"
  fi
else
  fuzz_rc=$?
  if grep -q '^SKIP:' "$LOG/coverage-fuzz.log"; then
    if [ "${LEANFZN_ALLOW_NO_ORACLE:-}" = "1" ]; then
      incomplete=1
      summary "coverage-fuzz: INCOMPLETE ($(head -1 "$LOG/coverage-fuzz.log"))"
    else
      failing "coverage-fuzz oracle missing ($(head -1 "$LOG/coverage-fuzz.log"))"
    fi
  else
    failing "coverage-fuzz (rc=$fuzz_rc; see $LOG/coverage-fuzz.log)"
  fi
fi

# --------------------------------------------------------------- summary
echo "=============================================="
if [ $fail -eq 0 ] && [ $incomplete -eq 0 ]; then
  echo "GATES: PASS  (logs: $LOG)"
  exit 0
elif [ $fail -eq 0 ]; then
  echo "GATES: INCOMPLETE (oracle evidence missing; logs: $LOG)"
  exit 3
fi
echo "GATES: FAIL  (logs: $LOG)"
exit 1
