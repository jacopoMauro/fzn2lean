#!/usr/bin/env python3
"""Regenerate `expected.txt` from the pinned MiniZinc 2.10.1 oracle.

This script is a *recorder*, not a judge: it runs every model exactly as
`run.sh` does and writes what the oracle printed.  The comparison that gives
the tests meaning is `run.sh` (or `test_upstream_assumptions.py`) replaying
`expected.txt`; this script exists so the recorded values can be reproduced
and audited, and so drifts after an oracle upgrade are visible as a diff.

Usage (oracle on PATH, runtime libraries visible):
    eval "$(bash audits/install_oracles.sh --print-env)"
    python3 Tests/Upstream/assumptions/make_expected.py

The oracle is invoked with `minizinc`; `LEANFZN_ORACLE_LIB=<prefix>/lib` is
honoured for the Qt/GL runtime, as in `run.sh`.
"""
import os
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent

# Models whose *outcome* is an upstream evaluation error, with the stderr
# substring that must identify it (the Lean interpretation makes the
# corresponding predicate false instead of erroring).  Every other model must
# evaluate cleanly.
ERROR_MODELS = {
    "int_div_zero.mzn": "division by zero",
    "int_pow_zero_negative.mzn": "negative power of zero is undefined",
}

MODELS = [
    "int_div.mzn",
    "int_mod.mzn",
    "int_div_zero.mzn",
    "int_pow.mzn",
    "int_pow_zero_negative.mzn",
    "set_le_lt.mzn",
    "set_le_lt_duplicates.mzn",
    "element_nonshifted.mzn",
    "element_nonshifted_shift.mzn",
]


def oracle_env():
    env = dict(os.environ)
    lib = env.get("LEANFZN_ORACLE_LIB", "")
    if lib:
        env["LD_LIBRARY_PATH"] = lib + (":" + env["LD_LIBRARY_PATH"]
                                        if env.get("LD_LIBRARY_PATH") else "")
    return env


def run(model):
    p = subprocess.run(["minizinc", str(HERE / model)],
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                       env=oracle_env())
    return p.stdout.decode(), p.stderr.decode()


def main():
    lines = [
        "# expected.txt — recorded upstream output of the G-series assumption models.",
        "#",
        "# Format, one record per model:",
        "#   === <file> ===        record header",
        "#   want: <text>          exact expected stdout; lines joined by \"|\";",
        "#                         the empty stdout is written as (empty)",
        "#   want-stderr: <text>   exact required stderr substring, or none",
        "#   --- end ---           record terminator",
        "#",
        "# Every record below was produced by `make_expected.py` against",
        "# MiniZinc 2.10.1 (build 33348285743) and is replayed by run.sh;",
        "# the values are what MiniZinc *evaluated*, not a property assertion.",
        "",
    ]
    for model in MODELS:
        out, err = run(model)
        want_out = out.replace("\n", "|")
        if want_out == "":
            want_out = "(empty)"
        else:
            want_out = want_out[:-1]  # drop the trailing separator
        check = ERROR_MODELS.get(model)
        if check is None:
            if err.strip():
                sys.exit(f"{model}: unexpected stderr:\n{err}")
            want_err = "none"
        else:
            if check not in err:
                sys.exit(f"{model}: stderr lacks {check!r}:\n{err}")
            want_err = check
        lines.append(f"=== {model} ===")
        lines.append(f"want: {want_out}")
        lines.append(f"want-stderr: {want_err}")
        lines.append("--- end ---")
        lines.append("")
    (HERE / "expected.txt").write_text("\n".join(lines))
    print(f"wrote {HERE / 'expected.txt'} ({len(MODELS)} records)")


if __name__ == "__main__":
    main()
