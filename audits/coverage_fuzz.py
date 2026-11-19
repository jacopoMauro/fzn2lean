#!/usr/bin/env python3
"""Deterministic coverage fuzzer for the LeanFzn Core solver (dev-only).

Usage:
  python3 audits/coverage_fuzz.py --seeds 50 --start 0 --out tmp/o3-fuzz-smoke
  python3 audits/coverage_fuzz.py --seeds 200 --out tmp/o3-fuzz
  python3 audits/coverage_fuzz.py --seeds 0 --extra-model MODEL.fzn \
      --binary tmp/o3-plant/bin/leanfzn-bug --out tmp/o3-plant/fuzz

The generator covers the O2 literal shapes, reified literal-result forms,
case-split ``var int`` patterns, unbounded ``var int`` whose bounds are forced
by the U1 case-split/linear rules, finite integer bounds, constant sets and set
variables (empty sets, reversed ranges, duplicated enumeration values,
out-of-range membership, set_in/set_in_reif/set_card/set_union/set_intersect/
array_var_set_element), ground constraints, element constraints with
out-of-range indices, and small MIN/MAX optimization models.  Every family
includes satisfiable and unsatisfiable variants where the family admits them.

For each model the tool runs ``leanfzn solve`` and ``fzn-gecode -a`` under a
wall cap, compares SAT/UNSAT verdicts, MIN/MAX optima, and the solution count
when the outputs are enumerable, and re-checks every emitted LeanFzn solution
with ``leanfzn check`` on the original model.  Gecode is an independent
development oracle only; it is never a solver dependency and never decides a
LeanFzn result.  A Core rejection (exit 2/3), unknown (exit 4) or timeout is
recorded as ``unsupported``/``unknown``/``timeout`` and is never counted as
agreement.  The summary reports the unsupported rate and the agreement
denominator explicitly.

Hard failures are ``wrong`` (verdict/optimum/count), ``boundEx`` (a printed
solution outside a claimed or oracle-proved bound) and ``rejectedWitness``.
On a disagreement a simple line-deletion reducer writes a smaller failing
model under the output directory.

``--require-oracle`` turns a missing ``fzn-gecode`` into a failure (exit 2)
instead of a ``SKIP``; the acceptance gate always passes it.  The summary names
every excluded (unsupported/unknown/timeout) case and prints per-family
agreement counts, so no generator family can be silently absent.
"""

from __future__ import annotations

import argparse
import json
import os
import random
import re
import shutil
import subprocess
import sys
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(HERE))

import strategy_matrix as sm  # noqa: E402  (sibling tool, not a package)

DEFAULT_BIN = ROOT / ".lake/build/bin/leanfzn"
HARD_KINDS = {"wrongVerdict", "wrongOptimum", "wrongSolutionCount",
              "boundEx", "rejectedWitness"}


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--seeds", type=int, required=True,
                   help="number of deterministic seeds (>=0)")
    p.add_argument("--start", type=int, default=0,
                   help="first seed value (default 0)")
    p.add_argument("--binary", default=str(DEFAULT_BIN))
    p.add_argument("--out", default=None,
                   help="output directory (default tmp/coverage_fuzz/<UTC>)")
    p.add_argument("--cap", type=int, default=10,
                   help="wall cap in seconds per solver call (default 10)")
    p.add_argument("--keep", action="store_true",
                   help="keep stdout/stderr/witness files for passing cases")
    p.add_argument("--extra-model", action="append", default=[],
                   help="additional FlatZinc model to run (repeatable)")
    p.add_argument("--no-reduce", action="store_true",
                   help="disable the failure reducer")
    p.add_argument("--require-oracle", action="store_true",
                   help="treat a missing fzn-gecode as a failure instead of "
                        "a SKIP (the acceptance gate uses this)")
    args = p.parse_args()
    if args.seeds < 0:
        p.error("--seeds must be >= 0")
    if args.start < 0:
        p.error("--start must be >= 0")
    if not 1 <= args.cap <= 300:
        p.error("--cap must be in 1..300")
    return args


# ---------------------------------------------------------------------------
# Model generators
# ---------------------------------------------------------------------------

def _decl_int(name: str, lo: int, hi: int) -> str:
    return f"var {lo}..{hi}: {name} :: output_var;\n"


def _decl_bool(name: str) -> str:
    return f"var bool: {name} :: output_var;\n"


def g_literal_int(rng: random.Random) -> list[tuple[str, str]]:
    a = rng.randint(-2, 2)
    b = a + rng.randint(1, 3)
    return [
        ("int_eq_true",
         f"constraint int_eq({a},{a});\nsolve satisfy;\n"),
        ("int_ne_false",
         f"constraint int_ne({a},{a});\nsolve satisfy;\n"),
        ("int_le_false",
         f"constraint int_le({b},{a});\nsolve satisfy;\n"),
    ]


def g_literal_reif(rng: random.Random) -> list[tuple[str, str]]:
    a = rng.randint(-1, 2)
    b = a + rng.randint(1, 2)
    head = _decl_bool("b")
    return [
        ("int_eq_reif_lit_true",
         head + f"constraint int_eq_reif({a},{a},true);\nsolve satisfy;\n"),
        ("int_eq_reif_lit_false",
         head + f"constraint int_eq_reif({a},{b},true);\nsolve satisfy;\n"),
        ("int_ne_reif_lit",
         head + f"constraint int_ne_reif({a},{b},false);\nsolve satisfy;\n"),
    ]


def g_literal_lin(rng: random.Random) -> list[tuple[str, str]]:
    c = rng.randint(-2, 2)
    return [
        ("lin_eq_true",
         f"constraint int_lin_eq([1,-1],[{c},{c}],0);\nsolve satisfy;\n"),
        ("lin_le_false",
         f"constraint int_lin_le([1,2],[{c},{c}],{3 * c - 1});\n"
         "solve satisfy;\n"),
        ("lin_ne_false",
         f"constraint int_lin_ne([1,1],[{c},{c}],{2 * c});\nsolve satisfy;\n"),
    ]


def g_literal_bool(rng: random.Random) -> list[tuple[str, str]]:
    head = _decl_bool("b")
    return [
        ("bool_eq_true", head + "constraint bool_eq(true,true);\n"
                                "solve satisfy;\n"),
        ("bool_eq_false", head + "constraint bool_eq(true,false);\n"
                                 "solve satisfy;\n"),
        ("bool_clause_true", head + "constraint bool_clause([true],[]);\n"
                                    "solve satisfy;\n"),
    ]


def g_set_in_const(rng: random.Random) -> list[tuple[str, str]]:
    x = _decl_int("x", 1, 3)
    card = rng.randint(1, 3)
    return [
        ("set_card", x + f"constraint set_card({{1,3}},{card});\n"
                         "solve satisfy;\n"),
        ("set_in_duplicate", x + "constraint set_in(x,{1,1});\n"
                                 "solve satisfy;\n"),
        ("set_in_empty", x + "constraint set_in(x,{});\nsolve satisfy;\n"),
        ("set_in_reversed", x + "constraint set_in(x,3..1);\n"
                                "solve satisfy;\n"),
        ("set_in_out_of_range", x + "constraint set_in(x,{4});\n"
                                    "solve satisfy;\n"),
    ]


def g_set_reif(rng: random.Random) -> list[tuple[str, str]]:
    x = _decl_int("x", 1, 3)
    b = _decl_bool("b")
    sat = (x + b + "constraint set_in_reif(x,{1,3},b);\n"
           "constraint bool_clause([b],[]);\nsolve satisfy;\n")
    unsat = (x + b + "constraint set_in_reif(x,{1,3},b);\n"
             "constraint bool_clause([b],[]);\n"
             "constraint int_eq(x,2);\nsolve satisfy;\n")
    lit = (x + "constraint set_in_reif(x,{1,3},true);\nsolve satisfy;\n")
    return [("sat", sat), ("unsat", unsat), ("literal_result", lit)]


def g_set_vars(rng: random.Random) -> list[tuple[str, str]]:
    s = "var set of 1..3: s :: output_var;\n"
    t = "var set of 1..3: t :: output_var;\n"
    arr = ("array [1..2] of var set of 1..3: ss = [s, t];\n")
    k = rng.randint(1, 3)
    return [
        ("set_card", s + f"constraint set_card(s,{k});\nsolve satisfy;\n"),
        ("set_union", s + t + "constraint set_union(s,t,{1,2,3});\n"
                              "solve satisfy;\n"),
        ("set_intersect", s + t + "constraint set_intersect(s,t,{2});\n"
                                  "solve satisfy;\n"),
        ("set_in_var", s + _decl_int("x", 1, 3) +
         "constraint set_in(x,s);\nsolve satisfy;\n"),
        ("array_var_set_element", s + t + arr +
         "constraint array_var_set_element(1,ss,t);\nsolve satisfy;\n"),
        ("empty_set_literal", s + "constraint set_in(1,{});\n"
                                  "solve satisfy;\n"),
    ]


def g_bool_var(rng: random.Random) -> list[tuple[str, str]]:
    b1 = _decl_bool("b1")
    b2 = _decl_bool("b2")
    return [
        ("bool_eq_sat", b1 + b2 + "constraint bool_eq(b1,b2);\n"
                                  "solve satisfy;\n"),
        ("bool_eq_unsat",
         b1 + b2 + "constraint bool_eq(b1,b2);\n"
         "constraint bool_clause([b1],[]);\n"
         "constraint bool_clause([],[b2]);\nsolve satisfy;\n"),
        ("bool_clause_sat",
         b1 + b2 + "constraint bool_clause([b1,b2],[]);\n"
         "solve satisfy;\n"),
        ("bool_clause_unsat",
         b1 + b2 + "constraint bool_clause([b1,b2],[]);\n"
         "constraint bool_clause([],[b1]);\n"
         "constraint bool_clause([],[b2]);\nsolve satisfy;\n"),
        ("bool_clause_mixed", b1 + b2 +
         "constraint bool_clause([b1],[b2]);\nsolve satisfy;\n"),
    ]


def g_reif_eq_ne(rng: random.Random) -> list[tuple[str, str]]:
    x = _decl_int("x", 1, 5)
    b = _decl_bool("b")
    value = rng.randint(2, 4)
    models = [
        ("eq_sat", x + b + f"constraint int_eq_reif(x,{value},b);\n"
         "constraint bool_clause([b],[]);\nsolve satisfy;\n"),
        ("eq_unsat", x + b + f"constraint int_eq_reif(x,{value},b);\n"
         "constraint bool_clause([b],[]);\n"
         f"constraint int_ne(x,{value});\nsolve satisfy;\n"),
        ("eq_lit_result",
         x + f"constraint int_eq_reif(x,{value},true);\nsolve satisfy;\n"),
        ("ne_sat", x + b + f"constraint int_ne_reif(x,{value},b);\n"
         "constraint bool_clause([b],[]);\nsolve satisfy;\n"),
        ("ne_unsat", x + b + f"constraint int_ne_reif(x,{value},b);\n"
         "constraint bool_clause([b],[]);\n"
         f"constraint int_eq(x,{value});\nsolve satisfy;\n"),
        ("eq_lit_arg",
         x + b + f"constraint int_eq_reif({value},x,b);\n"
         "constraint bool_clause([b],[]);\nsolve satisfy;\n"),
    ]
    return models


def g_reif_le(rng: random.Random) -> list[tuple[str, str]]:
    x = _decl_int("x", 1, 5)
    b = _decl_bool("b")
    k = rng.randint(2, 4)
    return [
        ("le_sat", x + b + f"constraint int_le_reif(x,{k},b);\n"
         "constraint bool_clause([b],[]);\nsolve satisfy;\n"),
        ("le_unsat", x + b + f"constraint int_le_reif(x,{k},b);\n"
         "constraint bool_clause([b],[]);\n"
         f"constraint int_ge(x,{k + 1});\nsolve satisfy;\n"),
        ("le_lit_result",
         x + f"constraint int_le_reif(x,{k},true);\nsolve satisfy;\n"),
        ("le_lit_arg",
         x + b + f"constraint int_le_reif({k},x,b);\nsolve satisfy;\n"),
    ]


def g_lin_reif(rng: random.Random) -> list[tuple[str, str]]:
    x = _decl_int("x", 1, 4)
    y = _decl_int("y", 1, 4)
    b = _decl_bool("b")
    xs = "array [1..2] of var int: xs = [x,y];\n"
    sat = (x + y + b + xs +
           "constraint int_lin_eq_reif([1,2],xs,5,b);\n"
           "constraint bool_clause([b],[]);\nsolve satisfy;\n")
    unsat = (x + y + b + xs +
             "constraint int_lin_eq_reif([1,2],xs,5,b);\n"
             "constraint bool_clause([b],[]);\n"
             "constraint int_eq(y,2);\nconstraint int_ne(x,1);\n"
             "solve satisfy;\n")
    le = (x + y + b + xs +
          "constraint int_lin_le_reif([1,1],xs,3,b);\n"
          "constraint bool_clause([b],[]);\nsolve satisfy;\n")
    ne = (x + y + b + xs +
          "constraint int_lin_ne_reif([1,1],xs,3,b);\n"
          "constraint bool_clause([b],[]);\nsolve satisfy;\n")
    ne_unsat = (x + y + b + xs +
                "constraint int_lin_ne_reif([1,1],xs,3,b);\n"
                "constraint bool_clause([b],[]);\n"
                "constraint int_eq(x,1);\nconstraint int_eq(y,2);\n"
                "solve satisfy;\n")
    return [("eq_sat", sat), ("eq_unsat", unsat), ("le_sat", le),
            ("ne_sat", ne), ("ne_unsat", ne_unsat)]


def g_case_split(rng: random.Random) -> list[tuple[str, str]]:
    x = _decl_int("x", 1, 6)
    b1 = _decl_bool("b1")
    b2 = _decl_bool("b2")
    a, c = rng.sample([1, 2, 3, 4, 5, 6], 2)
    base = (x + b1 + b2 +
            f"constraint int_eq_reif(x,{a},b1);\n"
            f"constraint int_eq_reif(x,{c},b2);\n"
            "constraint bool_clause([b1],[]);\n"
            "constraint bool_clause([],[b2]);\nsolve satisfy;\n")
    unsat = (x + b1 + b2 +
             f"constraint int_eq_reif(x,{a},b1);\n"
             f"constraint int_eq_reif(x,{c},b2);\n"
             "constraint bool_clause([b1],[]);\n"
             "constraint bool_clause([],[b2]);\n"
             f"constraint int_eq(x,{c});\nsolve satisfy;\n")
    return [("sat", base), ("unsat", unsat)]


def g_domains(rng: random.Random) -> list[tuple[str, str]]:
    lo = -rng.randint(1, 3)
    hi = rng.randint(1, 3)
    return [
        ("negative_sat",
         _decl_int("x", lo, hi) + "constraint int_le(x,0);\n"
         "solve satisfy;\n"),
        ("singleton_unsat",
         _decl_int("x", 0, 0) + "constraint int_ne(x,0);\n"
         "solve satisfy;\n"),
        ("negative_range",
         _decl_int("x", -5, -3) + "constraint int_ge(x,-4);\n"
         "solve satisfy;\n"),
        ("singleton_sat",
         _decl_int("x", 5, 5) + "constraint int_eq(x,5);\n"
         "solve satisfy;\n"),
    ]


def g_bounds(rng: random.Random) -> list[tuple[str, str]]:
    """Unbounded ``var int`` models whose finite bounds are forced by the
    U1 rules.  Gecode can solve these (the constraints bound the search
    space), so this group exercises the derivation differentially."""
    split = ("var int: x :: output_var;\n"
             "var bool: c :: output_var;\n"
             "var bool: r1 :: output_var;\n"
             "var bool: r2 :: output_var;\n"
             "constraint int_eq_reif(x,3,r1);\n"
             "constraint int_eq_reif(x,7,r2);\n"
             "constraint bool_clause([r1],[c]);\n"
             "constraint bool_clause([c,r2],[]);\n")
    split_unsat = (split + "constraint int_ne(x,3);\n"
                   "constraint int_ne(x,7);\nsolve satisfy;\n")
    var_anchor = ("var int: x :: output_var;\n"
                  "var 2..4: y :: output_var;\n"
                  "var bool: c :: output_var;\n"
                  "var bool: r1 :: output_var;\n"
                  "var bool: r2 :: output_var;\n"
                  "constraint int_eq_reif(x,y,r1);\n"
                  "constraint int_eq_reif(x,9,r2);\n"
                  "constraint bool_clause([r1],[c]);\n"
                  "constraint bool_clause([c,r2],[]);\n"
                  "solve satisfy;\n")
    linear_base = ("var int: x :: output_var;\n"
                   "var 0..1: y :: output_var;\n"
                   "constraint int_lin_eq([2,1],[x,y],7);\n")
    linear_pre = linear_base + "solve satisfy;\n"
    linear_post = ("var int: x :: output_var;\n"
                   "var 0..1: y :: output_var;\n"
                   "constraint int_lin_eq([1,2],[y,x],7);\n"
                   "solve satisfy;\n")
    linear_neg = ("var int: x :: output_var;\n"
                  "var 0..1: y :: output_var;\n"
                  "constraint int_lin_eq([-2,1],[x,y],-7);\n"
                  "solve satisfy;\n")
    linear_unsat = (linear_base + "constraint int_ne(x,3);\nsolve satisfy;\n")
    chain = ("var int: x :: output_var;\n"
             "var int: z :: output_var;\n"
             "var bool: c :: output_var;\n"
             "var bool: r1 :: output_var;\n"
             "var bool: r2 :: output_var;\n"
             "constraint int_eq_reif(x,3,r1);\n"
             "constraint int_eq_reif(x,7,r2);\n"
             "constraint bool_clause([r1],[c]);\n"
             "constraint bool_clause([c,r2],[]);\n"
             "constraint int_lin_eq([1,1],[z,x],10);\nsolve satisfy;\n")
    return [("split_sat", split + "solve satisfy;\n"),
            ("split_unsat", split_unsat),
            ("split_var_anchor", var_anchor),
            ("linear_pre_sat", linear_pre),
            ("linear_post_sat", linear_post),
            ("linear_neg_sat", linear_neg),
            ("linear_unsat", linear_unsat),
            ("chain_sat", chain)]


def g_element(rng: random.Random) -> list[tuple[str, str]]:
    i = _decl_int("i", 1, 2)
    x = _decl_int("x", 1, 3)
    y = _decl_int("y", 1, 3)
    arr = "array [1..2] of var int: ys = [x,y];\n"
    return [
        ("int_element_sat",
         i + x + "constraint array_int_element(i,[1,2],x);\n"
         "solve satisfy;\n"),
        ("var_element_sat",
         i + x + y + arr +
         "constraint array_var_int_element(i,ys,x);\nsolve satisfy;\n"),
        ("index_out_of_range",
         x + "constraint array_int_element(0,[1,2],x);\n"
         "solve satisfy;\n"),
        ("index_high_out_of_range",
         x + "constraint array_int_element(3,[1,2],x);\n"
         "solve satisfy;\n"),
        ("index_domain_out_of_range",
         _decl_int("i", 0, 3) + x +
         "constraint array_int_element(i,[1,2],x);\nsolve satisfy;\n"),
    ]


def g_ground(rng: random.Random) -> list[tuple[str, str]]:
    return [
        ("false_int_eq", "constraint int_eq(2,3);\nsolve satisfy;\n"),
        ("true_int_eq", "constraint int_eq(2,2);\nsolve satisfy;\n"),
        ("false_bool_eq",
         "constraint bool_eq(true,false);\nsolve satisfy;\n"),
        ("false_int_ne", "constraint int_ne(5,5);\nsolve satisfy;\n"),
    ]


def g_opt_min(rng: random.Random) -> list[tuple[str, str]]:
    x = _decl_int("x", 0, 4)
    y = _decl_int("y", 0, 3)
    xs = "array [1..2] of var int: xs = [x,y];\n"
    return [
        ("min_int", x + "constraint int_le(x,3);\nsolve minimize x;\n"),
        ("min_lin", x + y + xs +
         "constraint int_lin_le([1,1],xs,3);\nsolve minimize x;\n"),
        ("min_unsat", _decl_int("x", 0, 1) +
         "constraint int_eq(x,0);\nconstraint int_ne(x,0);\n"
         "solve minimize x;\n"),
    ]


def g_opt_max(rng: random.Random) -> list[tuple[str, str]]:
    x = _decl_int("x", 0, 4)
    y = _decl_int("y", 0, 3)
    xs = "array [1..2] of var int: xs = [x,y];\n"
    return [
        ("max_int", x + "constraint int_le(x,3);\nsolve maximize x;\n"),
        ("max_negative", _decl_int("x", -3, 0) + "solve maximize x;\n"),
        ("max_lin", x + y + xs +
         "constraint int_lin_le([1,1],xs,3);\nsolve maximize y;\n"),
        ("max_unsat", _decl_int("x", 0, 1) +
         "constraint int_eq(x,0);\nconstraint int_ne(x,0);\n"
         "solve maximize x;\n"),
    ]


GROUPS = [
    ("literal_int", g_literal_int),
    ("literal_reif", g_literal_reif),
    ("literal_lin", g_literal_lin),
    ("literal_bool", g_literal_bool),
    ("set_in_const", g_set_in_const),
    ("set_reif", g_set_reif),
    ("set_vars", g_set_vars),
    ("bool_var", g_bool_var),
    ("reif_eq_ne", g_reif_eq_ne),
    ("reif_le", g_reif_le),
    ("lin_reif", g_lin_reif),
    ("case_split", g_case_split),
    ("bounds", g_bounds),
    ("domains", g_domains),
    ("element", g_element),
    ("ground", g_ground),
    ("opt_min", g_opt_min),
    ("opt_max", g_opt_max),
]


# ---------------------------------------------------------------------------
# Running and classifying
# ---------------------------------------------------------------------------

def _text(value) -> str:
    if value is None:
        return ""
    if isinstance(value, bytes):
        return value.decode("utf-8", "replace")
    return str(value)


def oracle_env() -> dict[str, str]:
    """The child environment for the independent oracles.

    The pinned MiniZinc bundle ships its runtime libraries in `lib/`; the gate
    exports that prefix as `LEANFZN_ORACLE_LIB` instead of changing its own
    `LD_LIBRARY_PATH` (the bundle's stub libs would break sed/git/python), so
    the oracle children get it here.
    """
    env = dict(os.environ)
    lib = env.get("LEANFZN_ORACLE_LIB", "")
    if lib:
        env["LD_LIBRARY_PATH"] = lib + (":" + env["LD_LIBRARY_PATH"]
                                        if env.get("LD_LIBRARY_PATH") else "")
    return env


def run_capped(argv: list[str], cap: int, env: dict[str, str] | None = None) -> dict:
    start = time.monotonic()
    try:
        p = subprocess.run(argv, cwd=ROOT, stdout=subprocess.PIPE,
                           stderr=subprocess.PIPE, timeout=cap, env=env)
        return {"rc": p.returncode, "stdout": _text(p.stdout),
                "stderr": _text(p.stderr), "timed_out": False,
                "wall_s": time.monotonic() - start}
    except subprocess.TimeoutExpired as e:
        return {"rc": 124, "stdout": _text(e.stdout),
                "stderr": _text(e.stderr), "timed_out": True,
                "wall_s": time.monotonic() - start}
    except OSError as e:
        return {"rc": 127, "stdout": "", "stderr": str(e),
                "timed_out": False, "wall_s": time.monotonic() - start}


def split_blocks(text: str) -> list[list[str]]:
    blocks: list[list[str]] = []
    current: list[str] = []
    for line in text.splitlines():
        stripped = line.strip()
        if stripped == "----------":
            block = [ln for ln in current if ln.strip()]
            # Ground models have a valid empty assignment, still terminated
            # by the solution separator. Do not discard its SAT witness.
            blocks.append(block)
            current = []
        elif stripped == "==========":
            current = []
        else:
            current.append(line)
    return blocks


def classify_core(run: dict, kind: str | None) -> str:
    if run["timed_out"]:
        return "timeout"
    out = run["stdout"]
    rc = run["rc"]
    if "UNSATISFIABLE" in out:
        return "unsat"
    if rc == 3:
        return "unsupported"
    if rc == 4:
        return "unknown"
    if rc in (1, 2):
        return "rejected"
    if rc == 0:
        if "==========" in out:
            return "optimum" if kind else "complete"
        if split_blocks(out):
            return "sat"
        return "none"
    return "error"


def classify_gecode(run: dict, kind: str | None) -> str:
    if run["timed_out"]:
        return "timeout"
    out = run["stdout"]
    if "UNSATISFIABLE" in out:
        return "unsat"
    blocks = split_blocks(out)
    if run["rc"] == 0:
        if "==========" in out:
            return "optimum" if kind else "sat_complete"
        if blocks:
            return "sat_incomplete"
        return "none"
    return "unsupported"


def objective_of(block: list[str], var: str | None) -> int | None:
    value = sm.objective_value(block, var)
    try:
        return int(value) if value != "-" else None
    except ValueError:
        return None


def first_check_cores() -> str:
    try:
        cpus = sorted(os.sched_getaffinity(0))
    except (AttributeError, OSError):
        cpus = []
    return str(cpus[0]) if cpus else "0"


def safe_name(text: str) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]+", "_", text)[:160]


def evaluate(ctx: dict, model_path: Path, case_id: str,
             check_witness: bool = True) -> dict:
    kind = sm.model_info(model_path)[1]
    core = run_capped([str(ctx["binary"]), "solve", str(model_path)],
                      ctx["cap"])
    # fzn-gecode mmaps its input; some workspace filesystems (virtiofs) do not
    # support mmap, so feed it a byte-identical copy on the local temp dir.
    gecode_model = ctx["gecode_tmp"] / f"{case_id}.fzn"
    try:
        shutil.copyfile(model_path, gecode_model)
        gecode_path = gecode_model
    except OSError:
        gecode_path = model_path
    gecode = run_capped([ctx["gecode"], "-a", str(gecode_path)], ctx["cap"],
                        env=oracle_env())
    try:
        gecode_model.unlink()
    except OSError:
        pass
    core_claim = classify_core(core, kind)
    gecode_claim = classify_gecode(gecode, kind)
    core_blocks = split_blocks(core["stdout"])
    gecode_blocks = split_blocks(gecode["stdout"])

    runs = ctx["runs_dir"]
    core_out = runs / f"{case_id}.core.out"
    core_err = runs / f"{case_id}.core.err"
    gec_err = runs / f"{case_id}.gecode.err"
    core_out.write_text(core["stdout"], encoding="utf-8")
    core_err.write_text(core["stderr"], encoding="utf-8")
    gec_err.write_text(gecode["stderr"], encoding="utf-8")

    failures: list[dict] = []
    comparison = "skipped"
    comparable = False
    count_checked = False

    if check_witness:
        for i, block in enumerate(core_blocks):
            solpath = runs / f"{case_id}.witness{i}.txt"
            verdict = sm.check_solution(str(ctx["binary"]), str(model_path),
                                        block, solpath,
                                        ctx["cores"])
            if verdict != "yes":
                ctx["fail_dir"].mkdir(parents=True, exist_ok=True)
                kept = ctx["fail_dir"] / f"{case_id}.witness{i}.txt"
                kept.write_text("\n".join(block) + "\n----------\n",
                                encoding="utf-8")
                failures.append({
                    "kind": "rejectedWitness",
                    "detail": f"solution block {i} rejected ({verdict})",
                    "solution": str(kept),
                })
            elif not ctx["keep"]:
                try:
                    solpath.unlink()
                except OSError:
                    pass

    core_unsupported = core_claim in ("unsupported", "rejected")
    if core_unsupported:
        comparison = "unsupported"
    elif core_claim in ("unknown", "timeout", "none", "error"):
        comparison = f"core_{core_claim}"
    elif gecode_claim in ("timeout",):
        comparison = "oracle_timeout"
    elif gecode_claim in ("unsupported", "none"):
        comparison = "oracle_unsupported"
    elif core_claim == "unsat":
        comparable = True
        if gecode_claim in ("sat_complete", "sat_incomplete", "optimum"):
            failures.append({
                "kind": "wrongVerdict",
                "detail": f"Core UNSAT but Gecode {gecode_claim} "
                          f"({len(gecode_blocks)} solution(s))",
            })
            comparison = "wrong"
        else:
            comparison = "agree"
    elif gecode_claim == "unsat":
        comparable = True
        failures.append({
            "kind": "wrongVerdict",
            "detail": f"Core {core_claim} but Gecode UNSAT",
        })
        comparison = "wrong"
    elif kind is not None:
        # Optimization.
        obj_var = sm.model_info(model_path)[0]
        core_obj = objective_of(core_blocks[-1], obj_var) if core_blocks else None
        gec_obj = objective_of(gecode_blocks[-1], obj_var) if gecode_blocks else None
        if core_claim == "optimum":
            comparable = True
            if core_obj is None:
                comparison = "unparsed-objective"
            elif gecode_claim == "optimum" and gec_obj is not None:
                if core_obj != gec_obj:
                    failures.append({
                        "kind": "wrongOptimum",
                        "detail": f"Core optimum {core_obj} != Gecode "
                                  f"optimum {gec_obj}",
                    })
                    comparison = "wrong"
                else:
                    comparison = "agree"
            else:
                comparison = "oracle_incomplete"
        elif gecode_claim == "optimum" and gec_obj is not None:
            # Incumbent only: the verdict agrees; check the stated bound.
            comparable = True
            comparison = "agree"
        else:
            comparison = "oracle_incomplete"

        bounds = []
        if core_claim == "optimum" and core_obj is not None:
            bounds.append(("Core optimum", core_obj))
        if gecode_claim == "optimum" and gec_obj is not None:
            bounds.append(("Gecode optimum", gec_obj))
        for i, block in enumerate(core_blocks):
            obj = objective_of(block, obj_var)
            if obj is None:
                continue
            for label, bound in bounds:
                if (kind == "MIN" and obj < bound) or \
                   (kind == "MAX" and obj > bound):
                    failures.append({
                        "kind": "boundEx",
                        "detail": f"solution {i} objective {obj} is better "
                                  f"than {label} {bound}",
                    })
                    comparison = "boundEx"
    else:
        # Satisfaction.
        core_solutions = len({tuple(b) for b in core_blocks})
        if gecode_claim == "sat_complete":
            comparable = True
            count_checked = True
            gec_solutions = len({tuple(b) for b in gecode_blocks})
            if core_solutions > gec_solutions:
                failures.append({
                    "kind": "wrongSolutionCount",
                    "detail": f"Core printed {core_solutions} solution(s), "
                              f"Gecode enumerates only {gec_solutions}",
                })
                comparison = "wrong"
            elif core_claim == "complete" and \
                    core_solutions != gec_solutions:
                failures.append({
                    "kind": "wrongSolutionCount",
                    "detail": f"Core complete count {core_solutions} != "
                              f"Gecode {gec_solutions}",
                })
                comparison = "wrong"
            else:
                comparison = "agree"
        elif gecode_claim == "sat_incomplete":
            comparable = True
            comparison = "agree"
        else:
            comparison = "oracle_incomplete"

    if failures and failures[0]["kind"] in HARD_KINDS:
        if comparison != "wrong":
            comparison = failures[0]["kind"]

    result = {
        "id": case_id,
        "model": str(model_path.relative_to(ctx["out"])),
        "kind": kind,
        "core": {
            "rc": core["rc"], "claim": core_claim,
            "solutions": len(core_blocks),
            "timed_out": core["timed_out"],
            "stderr": core["stderr"].strip()[:500],
        },
        "gecode": {
            "rc": gecode["rc"], "claim": gecode_claim,
            "solutions": len(gecode_blocks),
            "timed_out": gecode["timed_out"],
            "stderr": gecode["stderr"].strip()[:500],
        },
        "comparison": comparison,
        "comparable": comparable,
        "count_checked": count_checked,
        "failures": failures,
    }
    if not ctx["keep"] and not failures:
        for path in (core_out, core_err, gec_err):
            try:
                path.unlink()
            except OSError:
                pass
    return result


# ---------------------------------------------------------------------------
# Reducer
# ---------------------------------------------------------------------------

def reduce_failure(ctx: dict, case: dict, result: dict) -> dict:
    text = (ctx["out"] / result["model"]).read_text(encoding="utf-8")
    lines = text.splitlines()
    original = "\n".join(lines) + "\n"
    original_kinds = {f["kind"] for f in result["failures"]}
    tmp_id = safe_name(case["id"] + "_reduce")
    tmp_path = ctx["runs_dir"] / f"{tmp_id}.fzn"
    runs = 0
    progress = True
    while progress:
        progress = False
        idx = 0
        while idx < len(lines):
            if not lines[idx].lstrip().startswith("constraint "):
                idx += 1
                continue
            candidate = lines[:idx] + lines[idx + 1:]
            if not candidate:
                idx += 1
                continue
            tmp_path.write_text("\n".join(candidate) + "\n", encoding="utf-8")
            reduced = evaluate(ctx, tmp_path, tmp_id, check_witness=False)
            runs += 1
            kinds = {f["kind"] for f in reduced["failures"]}
            if kinds & HARD_KINDS:
                lines = candidate
                original = "\n".join(lines) + "\n"
                original_kinds = kinds
                progress = True
                continue
            idx += 1
    try:
        tmp_path.unlink()
    except OSError:
        pass
    if original == "\n".join(text.splitlines()) + "\n":
        return {"reduced": False, "runs": runs,
                "failure_kinds": sorted(original_kinds)}
    ctx["fail_dir"].mkdir(parents=True, exist_ok=True)
    reduced_path = ctx["fail_dir"] / f"{result['id']}.reduced.fzn"
    reduced_path.write_text(original, encoding="utf-8")
    return {"reduced": True, "runs": runs,
            "failure_kinds": sorted(original_kinds),
            "path": str(reduced_path)}


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------

def build_cases(start: int, seeds: int) -> list[dict]:
    cases: list[dict] = []
    used: set[str] = set()
    for seed in range(start, start + seeds):
        group_name, fn = GROUPS[seed % len(GROUPS)]
        rng = random.Random(seed * 1000003 + 17)
        for suffix, text in fn(rng):
            case_id = f"{seed:05d}_{group_name}_{suffix}"
            while case_id in used:
                case_id += "_"
            used.add(case_id)
            cases.append({"id": case_id, "family": group_name,
                          "seed": seed, "text": text})
    return cases


def git_info() -> dict:
    def run(*args: str) -> str:
        try:
            return subprocess.run(list(args), cwd=ROOT, capture_output=True,
                                  text=True, timeout=10).stdout.strip()
        except (OSError, subprocess.SubprocessError):
            return ""
    return {"git_head": run("git", "rev-parse", "HEAD"),
            "git_status": run("git", "status", "--porcelain")}


def main() -> int:
    args = parse_args()
    binary = Path(args.binary)
    if not binary.is_absolute():
        binary = (ROOT / binary).resolve()
    if not binary.exists():
        print(f"coverage-fuzz: FAIL: binary not found: {binary}",
              file=sys.stderr)
        return 2

    gecode = shutil.which("fzn-gecode")
    # The pinned MiniZinc bundle ships its own runtime libraries in `lib/`
    # (see audits/install_oracles.sh); the gate exports the prefix rather than
    # changing its own LD_LIBRARY_PATH, so children get it here.
    oracle_lib = os.environ.get("LEANFZN_ORACLE_LIB", "")
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    out = Path(args.out) if args.out else ROOT / "tmp/coverage_fuzz" / stamp
    out.mkdir(parents=True, exist_ok=True)
    models_dir = out / "models"
    runs_dir = out / "runs"
    fail_dir = out / "failures"
    for d in (models_dir, runs_dir, fail_dir):
        d.mkdir(parents=True, exist_ok=True)

    cases = build_cases(args.start, args.seeds)
    for i, extra in enumerate(args.extra_model):
        path = Path(extra)
        if not path.is_absolute():
            path = (ROOT / path).resolve()
        if not path.exists():
            print(f"coverage-fuzz: FAIL: extra model not found: {path}",
                  file=sys.stderr)
            return 2
        text = path.read_text(encoding="utf-8")
        case_id = f"extra_{safe_name(path.stem)}_{i:02d}"
        cases.append({"id": case_id, "family": "extra", "seed": -1,
                      "text": text, "extra_path": str(path)})

    meta = {
        "tool": "audits/coverage_fuzz.py",
        "timestamp_utc": stamp,
        "binary": str(binary),
        "gecode": gecode,
        "gecode_all_solutions_flag": "-a",
        "cap_s": args.cap,
        "start": args.start,
        "seeds": args.seeds,
        "extra_models": args.extra_model,
        "keep": args.keep,
        "reduce": not args.no_reduce,
        "cases": len(cases),
        **git_info(),
    }
    (out / "meta.json").write_text(json.dumps(meta, indent=1) + "\n",
                                   encoding="utf-8")

    if gecode is None:
        report = {
            "tool": "audits/coverage_fuzz.py",
            "skipped": True,
            "reason": "fzn-gecode not found on PATH; no comparison possible",
            "models": len(cases),
            "require_oracle": args.require_oracle,
            "meta": meta,
        }
        (out / "report.json").write_text(json.dumps(report, indent=1) + "\n",
                                        encoding="utf-8")
        print("SKIP: fzn-gecode not found on PATH; coverage comparisons "
              "were not run. Install fzn-gecode to enable the fuzz oracle.")
        if args.require_oracle:
            print("coverage-fuzz: FAIL: --require-oracle was given but "
                  "fzn-gecode is not on PATH", file=sys.stderr)
            return 2
        return 0

    if not cases:
        print("coverage-fuzz: FAIL: no models generated "
              "(--seeds 0 with no --extra-model)")
        return 2

    gecode_tmp = Path(tempfile.mkdtemp(prefix="coverage-fuzz-gecode-"))
    ctx = {
        "binary": binary,
        "gecode": gecode,
        "cap": args.cap,
        "keep": args.keep,
        "out": out,
        "runs_dir": runs_dir,
        "fail_dir": fail_dir,
        "gecode_tmp": gecode_tmp,
        "cores": first_check_cores(),
    }

    results: list[dict] = []
    print(f"coverage-fuzz: {len(cases)} models, binary={binary}, "
          f"gecode={gecode}, cap={args.cap}s", flush=True)
    for i, case in enumerate(cases, 1):
        model_path = models_dir / f"{case['id']}.fzn"
        model_path.write_text(case["text"], encoding="utf-8")
        result = evaluate(ctx, model_path, case["id"])
        result["family"] = case["family"]
        result["seed"] = case["seed"]
        results.append(result)
        status = "OK"
        if any(f["kind"] in HARD_KINDS for f in result["failures"]):
            status = "FAIL"
        print(f"[{i:4d}/{len(cases)}] {case['id']}: "
              f"core={result['core']['claim']} "
              f"gecode={result['gecode']['claim']} -> {status} "
              f"({result['comparison']})", flush=True)

    if not args.no_reduce:
        for case, result in zip(cases, results):
            if any(f["kind"] in HARD_KINDS for f in result["failures"]):
                case_model = out / result["model"]
                if case_model.exists():
                    result["reduction"] = reduce_failure(ctx, case, result)

    models = len(results)
    comparisons = sum(1 for r in results if r["comparable"])
    agree = sum(1 for r in results if r["comparison"] == "agree")
    wrong = sum(1 for r in results for f in r["failures"]
                if f["kind"].startswith("wrong"))
    bound_ex = sum(1 for r in results for f in r["failures"]
                   if f["kind"] == "boundEx")
    rejected = sum(1 for r in results for f in r["failures"]
                   if f["kind"] == "rejectedWitness")
    unsupported = sum(1 for r in results
                      if r["comparison"] == "unsupported")
    unknown = sum(1 for r in results
                  if r["comparison"] in ("core_unknown", "core_none",
                                         "core_error"))
    timeouts = sum(1 for r in results
                   if r["comparison"] in ("core_timeout", "oracle_timeout"))
    oracle_unsupported = sum(1 for r in results
                             if r["comparison"] == "oracle_unsupported")
    oracle_incomplete = sum(1 for r in results
                            if r["comparison"] == "oracle_incomplete")
    # Every non-agreement must be attributable to a named family: the summary
    # lists each unsupported/unknown/timeout case so a silent regression in a
    # family cannot hide behind an aggregate count.
    by_family: dict[str, dict[str, int]] = {}
    for r in results:
        fam = by_family.setdefault(r["family"], {
            "models": 0, "agree": 0, "unsupported": 0, "unknown": 0,
            "timeouts": 0, "oracle_incomplete": 0, "oracle_unsupported": 0,
            "wrong": 0, "boundEx": 0, "rejectedWitness": 0})
        fam["models"] += 1
        if r["comparison"] == "agree":
            fam["agree"] += 1
        elif r["comparison"] == "unsupported":
            fam["unsupported"] += 1
        elif r["comparison"] in ("core_unknown", "core_none", "core_error"):
            fam["unknown"] += 1
        elif r["comparison"] in ("core_timeout", "oracle_timeout"):
            fam["timeouts"] += 1
        elif r["comparison"] == "oracle_incomplete":
            fam["oracle_incomplete"] += 1
        elif r["comparison"] == "oracle_unsupported":
            fam["oracle_unsupported"] += 1
        for f in r["failures"]:
            if f["kind"].startswith("wrong"):
                fam["wrong"] += 1
            elif f["kind"] in ("boundEx", "rejectedWitness"):
                fam[f["kind"]] += 1
    family_names = [name for name, _ in GROUPS]
    extra_names = sorted(set(by_family) - set(family_names))
    missing_families = [name for name in family_names
                        if name not in by_family]
    excluded = []
    for r in results:
        if r["comparison"] in ("unsupported", "core_unknown", "core_none",
                               "core_error", "core_timeout", "oracle_timeout"):
            excluded.append({"id": r["id"], "family": r["family"],
                             "comparison": r["comparison"]})

    counts = {
        "models": models,
        "comparisons": comparisons,
        "agree": agree,
        "wrong": wrong,
        "boundEx": bound_ex,
        "rejectedWitness": rejected,
        "unsupported": unsupported,
        "unknown": unknown,
        "timeouts": timeouts,
        "oracle_unsupported": oracle_unsupported,
        "oracle_incomplete": oracle_incomplete,
        "unsupported_rate": (unsupported / models) if models else 0.0,
        "agreement_rate": (agree / comparisons) if comparisons else None,
        "families_all_present": not missing_families,
        "missing_families": missing_families,
        "by_family": {name: by_family[name] for name in
                      family_names + extra_names},
        "excluded_cases": excluded,
    }
    report = {
        "tool": "audits/coverage_fuzz.py",
        "skipped": False,
        "meta": meta,
        "counts": counts,
        "cases": results,
    }
    (out / "report.json").write_text(json.dumps(report, indent=1) + "\n",
                                    encoding="utf-8")

    agreement_text = ("n/a" if counts["agreement_rate"] is None
                      else f"{counts['agreement_rate']:.4f}")
    lines = [
        f"O3 coverage fuzz: {out}",
        f"binary: {binary}",
        f"oracle: {gecode} -a (all solutions where enumerable)",
        f"FUZZ SUMMARY models={models} comparisons={comparisons} "
        f"agree={agree} unsupported={unsupported} "
        f"unsupported_rate={counts['unsupported_rate']:.4f} "
        f"unknown={unknown} timeouts={timeouts} "
        f"oracle_unsupported={oracle_unsupported} "
        f"oracle_incomplete={oracle_incomplete}",
        f"FUZZ HARD wrong/boundEx/rejectedWitness="
        f"{wrong}/{bound_ex}/{rejected}",
        f"agreement_denominator={comparisons} "
        f"agreement_rate={agreement_text}",
        "FUZZ FAMILIES " + " ".join(
            f"{name}={by_family[name]['agree']}/{by_family[name]['models']}"
            for name in family_names + extra_names),
        f"FUZZ FAMILIES-MISSING "
        f"{','.join(missing_families) if missing_families else 'none'}",
        "unsupported is never counted as agreement",
    ]
    lines.append(f"FUZZ UNSUPPORTED {unsupported} case(s): "
                 + (", ".join(f"{e['id']}({e['comparison']})"
                               for e in excluded) if excluded else "none"))
    if any(r["failures"] for r in results):
        lines.append("failures:")
        for r in results:
            for f in r["failures"]:
                lines.append(f"  - {r['id']} {f['kind']}: {f['detail']}")
    summary = "\n".join(lines) + "\n"
    (out / "summary.txt").write_text(summary, encoding="utf-8")
    shutil.rmtree(gecode_tmp, ignore_errors=True)
    print(summary, end="")
    print(f"report: {out / 'report.json'}")

    if counts["missing_families"]:
        print("coverage-fuzz: WARNING: no model covered family "
              + ", ".join(counts["missing_families"])
              + " (increase --seeds to cover every generator family)",
              file=sys.stderr)

    hard = wrong + bound_ex + rejected
    return 0 if hard == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
