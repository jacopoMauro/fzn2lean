#!/usr/bin/env bash
#
# File: audits/run_axiom_audit.sh
#
# Fail-closed CI axiom audit: runs the certified-axiom profile queries
# (or reads a pre-captured output file, for testing the audit itself)
# and validates that
#   (a) Lean exited 0 and produced output,
#   (b) EVERY expected theorem profile is present (exactly EXPECTED
#       profiles; multiline profiles are wrapped, so we join lines
#       first), with no duplicates,
#   (c) every axiom is in the allowlist
#       {propext, Classical.choice, Quot.sound},
#   (d) no sorryAx appears anywhere.
#
# Usage: audits/run_axiom_audit.sh [output-file]
#   Without an argument, a fresh `lake env lean
#   audits/certified_axioms.lean` run is captured and audited.
#   With an argument, the given file's contents are audited instead
#   (used to test this script's failure modes with fabricated
#   output; the file must already exist and be non-empty).
#
# Exit codes: 0 = audit passed; 1 = audit FAILED (any reason).

set -o pipefail

# The number of `#print axioms` queries in certified_axioms.lean. The
# audit is fail-closed: this is cross-checked against the source, so
# adding a query without bumping the expectation fails the audit.
AUDIT_SOURCE="$(cd "$(dirname "$0")" && pwd)/certified_axioms.lean"
EXPECTED="$(grep -c '^#print axioms' "$AUDIT_SOURCE" 2>/dev/null || echo 0)"
if [ "$EXPECTED" -lt 1 ]; then
  echo "ERROR: cannot read audit source $AUDIT_SOURCE (no #print axioms queries found)"
  exit 1
fi

ALLOWED='^(propext|Classical\.choice|Quot\.sound)$'
TMPDIR_AUDIT="$(mktemp -d)"
trap 'rm -rf "$TMPDIR_AUDIT"' EXIT
OUTPUT="$TMPDIR_AUDIT/profiles.txt"

if [ "$#" -ge 1 ]; then
  # Test mode: audit a pre-captured (possibly fabricated) output file.
  if [ ! -s "$1" ]; then
    echo "ERROR: axiom audit input '$1' is missing or empty"
    exit 1
  fi
  cp "$1" "$OUTPUT"
else
  # Normal mode: fresh run of the profile queries. Lean failure,
  # timeout, or empty output all fail the audit (fail-closed).
  REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
  (cd "$REPO_ROOT" && timeout 500 lake env lean "$AUDIT_SOURCE") \
      > "$OUTPUT" 2> "$TMPDIR_AUDIT/stderr.txt"
  AUDIT_EXIT=$?
  if [ "$AUDIT_EXIT" -ne 0 ]; then
    echo "ERROR: lake env lean $AUDIT_SOURCE failed (exit $AUDIT_EXIT); audit fails closed"
    cat "$OUTPUT" >&2
    cat "$TMPDIR_AUDIT/stderr.txt" >&2
    exit 1
  fi
  if [ ! -s "$OUTPUT" ]; then
    echo "ERROR: axiom audit produced empty output"
    exit 1
  fi
fi

# ---- Validation -------------------------------------------------------

# (d) no sorryAx anywhere in the raw output
if grep -q 'sorryAx' "$OUTPUT"; then
  echo "ERROR: sorryAx found in the axiom audit output"
  exit 1
fi

# (b) every expected theorem produces a profile; profiles may wrap
# across lines (Lean breaks long bracket lists), so join everything
# into one line first, then extract each 'depends on axioms: [...]'
# group.
# Lean uses a different sentence for an empty axiom set. Normalize that
# valid profile before counting and matching theorem names.
JOINED="$(tr '\n' ' ' < "$OUTPUT" | sed 's/ does not depend on any axioms/ depends on axioms: []/g')"
# Guard against grep failure producing an empty variable with
# pipefail; use a plain grep (the character class is greedy-safe
# because axiom lists never contain ']').
GROUPS_FILE="$TMPDIR_AUDIT/groups.txt"
grep -o "depends on axioms: \[[^]]*\]" > "$GROUPS_FILE" <<< "$JOINED" \
  || true
PROFILES=0
if [ -s "$GROUPS_FILE" ]; then
  PROFILES=$(grep -c . "$GROUPS_FILE")
fi
if [ "$PROFILES" -lt "$EXPECTED" ]; then
  echo "ERROR: expected $EXPECTED axiom profiles, found only $PROFILES (missing or malformed profiles)"
  exit 1
fi
if [ "$PROFILES" -gt "$EXPECTED" ]; then
  echo "ERROR: expected $EXPECTED axiom profiles, found $PROFILES (duplicates?)"
  exit 1
fi

# ---- Identity check (R1: substitution/duplication hardening) ----------
# Extract the EXPECTED theorem names from the audit source's
# `#print axioms NAME` lines, and the ACTUAL resolved names from
# the output's quoted headers ('Full.Name' depends on ...).
# Every expected name must match exactly one actual (exact or
# dot-suffix: the source uses unqualified names, Lean resolves
# them), and every actual must be claimed by exactly one expected
# (no substitution, no extras, no duplicates).
EXPECTED_ALL="$(sed -n 's/^#print axioms[[:space:]]\+\([^[:space:]].*\)[[:space:]]*$/\1/p' "$AUDIT_SOURCE")"
EXPECTED_NAMES="$(printf '%s\n' "$EXPECTED_ALL" | grep -c . || true)"
if [ "$EXPECTED_NAMES" -ne "$EXPECTED" ]; then
  echo "ERROR: audit source malformed: $EXPECTED query lines vs $EXPECTED_NAMES parsed names"
  exit 1
fi
ACTUAL_ALL="$(grep -oE "'[^']+' depends on axioms: \[[^]]*\]" <<< "$JOINED" \
  | sed "s/^'//; s/' depends.*$//")"
ACTUAL_NAMES="$(printf '%s\n' "$ACTUAL_ALL" | grep -c . || true)"
if [ "$ACTUAL_NAMES" -ne "$PROFILES" ]; then
  echo "ERROR: profile header parse mismatch ($PROFILES profiles vs $ACTUAL_NAMES parsed names; malformed output)"
  exit 1
fi
found_all=1
while IFS= read -r want; do
  [ -n "$want" ] || continue
  uses=0
  while IFS= read -r act; do
    [ -n "$act" ] || continue
    if [[ "$act" == "$want" || "$act" == *."$want" ]]; then
      uses=$((uses+1))
    fi
  done <<< "$ACTUAL_ALL"
  if [ "$uses" -eq 0 ]; then
    echo "ERROR: missing expected theorem profile: '$want'"
    found_all=0
  elif [ "$uses" -gt 1 ]; then
    echo "ERROR: ambiguous/duplicate match: expected '$want' matches $uses profiles"
    found_all=0
  fi
done <<< "$EXPECTED_ALL"
if [ "$found_all" -ne 1 ]; then
  exit 1
fi
# Injectivity: every ACTUAL profile is claimed by exactly one
# expected theorem (an unclaimed actual is an extra/substitution).
while IFS= read -r act; do
  [ -n "$act" ] || continue
  uses=0
  while IFS= read -r want; do
    [ -n "$want" ] || continue
    if [[ "$act" == "$want" || "$act" == *."$want" ]]; then
      uses=$((uses+1))
    fi
  done <<< "$EXPECTED_ALL"
  if [ "$uses" -eq 0 ]; then
    echo "ERROR: extra/unclaimed theorem profile: '$act'"
    exit 1
  fi
done <<< "$ACTUAL_ALL"

# (c) every axiom is in the allowlist
BAD_AXIOMS="$(sed 's/depends on axioms: \[//; s/\]$//' "$GROUPS_FILE" \
  | tr ',' '\n' | sed 's/^ *//; s/ *$//' | grep -v '^$' \
  | sort -u | grep -Ev "$ALLOWED" || true)"
if [ -n "$BAD_AXIOMS" ]; then
  echo "ERROR: unexpected axiom(s) outside the allowlist (propext, Classical.choice, Quot.sound):"
  echo "$BAD_AXIOMS"
  exit 1
fi

echo "axiom audit PASSED: $PROFILES/$EXPECTED theorem profiles, allowlist-only axioms, no sorryAx"
exit 0
