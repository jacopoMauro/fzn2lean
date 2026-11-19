#!/usr/bin/env python3
"""Fixed-conflict-limit A/B comparison for LeanFzn (PLAN C2/G1).

Runs two binaries (or two flag sets on one binary) over a cohort, each with the
same deterministic ``--conflict-limit=K`` (or a per-case limit from a case
table), and compares the deterministic search counters, terminal result, exit
class and objective metadata.  Every emitted witness is checked against the
source model with the ``leanfzn check`` front door from both binaries.

Usage (old-style model list; unchanged):
  audits/fixed_k.py --cohort audits/cohorts/T10.txt --limit 300 \
      --binary-a tmp/baseline/leanfzn-7e9c730e --binary-b .lake/build/bin/leanfzn \
      --out tmp/performance/g1-smoke

Usage (release cohort with declared expectations):
  audits/fixed_k.py --cohort-tsv audits/release_cohort.tsv --limit 10 \
      --binary-a tmp/release/ID/pgo/.lake/build/bin/leanfzn \
      --binary-b tmp/release/ID/nopgo/.lake/build/bin/leanfzn \
      --json tmp/release/ID/fixed_k/fixed_k.json --no-taskset

The exit status is 0 only when every case passes; 1 when a case fails
(missing/malformed stats, timeout, unexpected outcome, objective mismatch,
counter mismatch, rejected witness, ...), and 2 on setup errors (bad CLI,
missing/unreadable binary or checker, missing fixture, malformed cohort,
empty cohort, parallel/time-limited flags, lock busy).

Every failure is fail-closed: a timeout, an equal pair of missing counters, an
equal pair of external timeouts and an unverified witness are never a pass.
Exact action-counter equality is required for deterministic single-worker
cases and always for a same-binary identity run; it is not demanded when a
case declares ``exact_counters=false`` (portfolio/time-limited semantics must
be validated separately, and parallel or wall-time-limited flags are rejected
by this deterministic comparator anyway).

The per-case TSV columns are the historical ones followed by audit columns:
  case, outcome_a, outcome_b, wall_a, wall_b, ratio_b_over_a,
  counters_equal, differing, objective_a, objective_b, solutions_a,
  solutions_b, case_id, mode, expected_class, known_answer, exact_counters,
  objective_var, exit_a, exit_b, witnesses_checked, failures
Wall times are wall-clock seconds around the subprocess; the conflict limit is
the deterministic quantity, so a wall difference is only accepted with identical
counters.
"""

from __future__ import annotations

import argparse
import csv
import fcntl
import hashlib
import json
import os
import re
import shlex
import shutil
import signal
import subprocess
import sys
import time
from dataclasses import dataclass, replace
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_BIN = ROOT / ".lake/build/bin/leanfzn"
MEASURE_LOCK = "/tmp/fzn2lean-measure.lock"

COUNTERS = [
    "decisions", "conflicts", "learned", "propagations",
    "learnedLitsBefore", "learnedLitsAfter", "maxLevel", "rounds",
    "reasonsTrimmed",
]
ACTION_KEYS = ["decisions", "conflicts", "learned", "propagations",
               "learnedLitsBefore", "learnedLitsAfter", "maxLevel"]
# C6 (reason trimming) additionally requires the trim counter to be
# unchanged; it is deterministic but is not a search-action counter.  Seed
# metadata is compared when the solver reports it, so two runs cannot pass
# with different seed selections hidden behind identical action counters.
AUX_KEYS = ["reasonsTrimmed", "seeds"]
MANDATORY_STATS = COUNTERS + ["incumbents", "complete", "gaveUp"]

# Terminal classes accepted in a release case table.
EXPECTED_CLASSES = {"sat", "unsat", "optimal", "incomplete"}
MODES = {"satisfy", "minimize", "maximize"}
# A hard known answer (UNSAT or a proved optimum) needs an independent source;
# SAT may be witnessed by a checked solution; incomplete carries no claim.
KNOWN_SOURCES = {"exhaustive", "independent", "witness", "none"}
HARD_SOURCES = {"exhaustive", "independent"}

MARKER_UNSAT = "=====UNSATISFIABLE====="
MARKER_OPTIMUM = "=========="
MARKER_UNKNOWN = "=====UNKNOWN====="
MARKER_UNBOUNDED = "=====UNBOUNDED====="
MARKER_UNSAT_OR_UNBOUNDED = "=====UNSATorUNBOUNDED====="
MARKER_ERROR = "=====ERROR====="
KNOWN_MARKERS = {
    MARKER_UNSAT, MARKER_OPTIMUM, MARKER_UNKNOWN, MARKER_UNBOUNDED,
    MARKER_UNSAT_OR_UNBOUNDED, MARKER_ERROR,
}

CASE_TSV_COLUMNS = [
    "case_id", "model", "mode", "expected_class", "known_answer",
    "exact_counters", "known_answer_source",
]


@dataclass(frozen=True)
class CaseSpec:
    case_id: str
    model: str
    mode: str = "auto"
    expected_class: str | None = None
    known_answer: int | None = None
    exact_counters: bool = True
    known_answer_source: str | None = None
    conflict_limit: int | None = None


class SetupError(Exception):
    """A fail-closed setup/cohort error (exit 2)."""


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--cohort", action="append", default=None,
                   help="file with one model path per line; repeatable")
    p.add_argument("--cohort-tsv", default=None,
                   help="case table with declared expectations "
                        "(mutually exclusive with --cohort)")
    p.add_argument("--limit", type=int, required=True,
                   help="default conflict limit passed to both sides (1..)")
    p.add_argument("--binary-a", default=str(DEFAULT_BIN))
    p.add_argument("--binary-b", default=None,
                   help="second binary (default: same as --binary-a)")
    p.add_argument("--checker-a", default=None,
                   help="checker binary for side A (default: binary A)")
    p.add_argument("--checker-b", default=None,
                   help="checker binary for side B (default: binary B)")
    p.add_argument("--flags-a", default="",
                   help="extra solver flags for side A, shell-quoted")
    p.add_argument("--flags-b", default="",
                   help="extra solver flags for side B, shell-quoted")
    p.add_argument("--cap", type=int, default=120,
                   help="external wall cap per run in seconds (default 120)")
    p.add_argument("--out", default=None,
                   help="output directory (default tmp/performance/fixed_k/<UTC>)")
    p.add_argument("--json", default=None,
                   help="JSON report path (default OUT/fixed_k.json)")
    p.add_argument("--root", default=str(ROOT),
                   help="working/model root (default: repository root)")
    p.add_argument("--core", type=int, default=5,
                   help="CPU core for taskset (default 5)")
    p.add_argument("--no-taskset", action="store_true",
                   help="do not pin to --core (triage only)")
    p.add_argument("--require-equal-flags", action="store_true",
                   help="fail setup if --flags-a and --flags-b differ")
    p.add_argument("--lock", default=MEASURE_LOCK)
    p.add_argument("--quiet", action="store_true")
    args = p.parse_args()
    if args.limit < 1:
        p.error("--limit must be >= 1")
    if args.cap < 1:
        p.error("--cap must be >= 1")
    if args.binary_b is None:
        args.binary_b = args.binary_a
    if args.checker_a is None:
        args.checker_a = args.binary_a
    if args.checker_b is None:
        args.checker_b = args.binary_b
    if args.cohort and args.cohort_tsv:
        p.error("use either --cohort or --cohort-tsv, not both")
    if not args.cohort and not args.cohort_tsv:
        p.error("one of --cohort or --cohort-tsv is required")
    return args


def _truth(value: str) -> bool:
    v = value.strip().lower()
    if v in {"1", "true", "yes", "y"}:
        return True
    if v in {"0", "false", "no", "n"}:
        return False
    raise SetupError(f"invalid boolean value {value!r}")


def _int_or_none(value: str, what: str) -> int | None:
    v = value.strip()
    if v == "-":
        return None
    if not re.fullmatch(r"[+-]?\d+", v):
        raise SetupError(f"invalid {what} {value!r}")
    return int(v)


def load_cohort_tsv(path: str) -> list[CaseSpec]:
    """Load a committed case table, rejecting malformed rows fail-closed."""
    p = Path(path)
    if not p.is_file():
        raise SetupError(f"case table not found: {path}")
    try:
        text = p.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as exc:
        raise SetupError(f"cannot read case table {path}: {exc}") from exc
    raw = []
    for lineno, line in enumerate(text.splitlines(), 1):
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        raw.append((lineno, line))
    if not raw:
        raise SetupError(f"empty case table: {path}")
    reader = csv.reader([line for _, line in raw], delimiter="\t")
    rows = list(reader)
    header = [h.strip() for h in rows[0]]
    missing = [c for c in CASE_TSV_COLUMNS if c not in header]
    if missing:
        raise SetupError(f"case table {path} missing columns: "
                         f"{', '.join(missing)}")
    if len(set(header)) != len(header):
        raise SetupError(f"case table {path} has duplicate columns")
    idx = {name: header.index(name) for name in CASE_TSV_COLUMNS}

    specs: list[CaseSpec] = []
    seen_ids: set[str] = set()
    seen_models: set[str] = set()
    for row, (lineno, _) in zip(rows[1:], raw[1:]):
        if len(row) != len(header):
            raise SetupError(
                f"case table {path}:{lineno}: expected {len(header)} columns, "
                f"got {len(row)}")
        vals = {name: row[idx[name]].strip() for name in CASE_TSV_COLUMNS}
        cid = vals["case_id"]
        if not cid:
            raise SetupError(f"case table {path}:{lineno}: empty case_id")
        if cid in seen_ids:
            raise SetupError(f"case table {path}:{lineno}: duplicate case_id {cid!r}")
        seen_ids.add(cid)
        model = vals["model"]
        if not model:
            raise SetupError(f"case table {path}:{lineno}: empty model")
        if model in seen_models:
            raise SetupError(f"case table {path}:{lineno}: duplicate model {model!r}")
        seen_models.add(model)
        mode = vals["mode"]
        if mode not in MODES:
            raise SetupError(
                f"case table {path}:{lineno}: mode must be one of "
                f"{sorted(MODES)}, got {mode!r}")
        expected = vals["expected_class"]
        if expected not in EXPECTED_CLASSES:
            raise SetupError(
                f"case table {path}:{lineno}: expected_class must be one of "
                f"{sorted(EXPECTED_CLASSES)}, got {expected!r}")
        known = _int_or_none(vals["known_answer"], "known_answer")
        exact = _truth(vals["exact_counters"])
        source = vals["known_answer_source"]
        if source not in KNOWN_SOURCES:
            raise SetupError(
                f"case table {path}:{lineno}: known_answer_source must be one "
                f"of {sorted(KNOWN_SOURCES)}, got {source!r}")
        if expected in {"unsat", "optimal"} and source not in HARD_SOURCES:
            raise SetupError(
                f"case table {path}:{lineno}: {expected} needs exhaustive or "
                f"independent known-answer evidence, got {source!r}")
        if expected == "sat" and source == "none":
            raise SetupError(
                f"case table {path}:{lineno}: sat needs a witness or "
                f"independent source, not none")
        if expected == "optimal":
            if mode == "satisfy":
                raise SetupError(
                    f"case table {path}:{lineno}: optimal requires an "
                    f"optimization mode")
            if known is None:
                raise SetupError(
                    f"case table {path}:{lineno}: optimal requires a known "
                    f"answer")
        elif expected == "sat":
            if mode != "satisfy":
                raise SetupError(
                    f"case table {path}:{lineno}: sat requires mode satisfy")
            if known is not None:
                raise SetupError(
                    f"case table {path}:{lineno}: satisfy has no known "
                    f"objective")
        elif known is not None:
            raise SetupError(
                f"case table {path}:{lineno}: {expected} cannot claim a "
                f"known objective")
        limit = None
        if "conflict_limit" in header:
            raw_limit = row[header.index("conflict_limit")].strip()
            if raw_limit:
                limit = _int_or_none(raw_limit, "conflict_limit")
                if limit is None or limit < 1:
                    raise SetupError(
                        f"case table {path}:{lineno}: conflict_limit must be "
                        f"positive")
        specs.append(CaseSpec(
            case_id=cid, model=model, mode=mode, expected_class=expected,
            known_answer=known, exact_counters=exact,
            known_answer_source=source, conflict_limit=limit))
    if not specs:
        raise SetupError(f"case table has no data rows: {path}")
    return specs


def cases_from(paths: list[str]) -> list[str]:
    cases: list[str] = []
    for path in paths:
        p = Path(path)
        if not p.is_file():
            raise SetupError(f"cohort not found: {path}")
        try:
            text = p.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError) as exc:
            raise SetupError(f"cannot read cohort {path}: {exc}") from exc
        for line in text.splitlines():
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            cases.append(line)
    return cases


def model_solve(model_path: Path) -> tuple[str, str | None]:
    """Return (satisfy|minimize|maximize, objective variable or None)."""
    try:
        text = model_path.read_text(encoding="utf-8", errors="replace")
    except OSError as exc:
        raise SetupError(f"cannot read model {model_path}: {exc}") from exc
    m = re.search(r"(?ms)^\s*solve\b([^;]*);", text)
    if not m:
        raise SetupError(f"model has no solve item: {model_path}")
    body = m.group(1)
    objectives = re.findall(
        r"\b(minimize|maximize)\s+([A-Za-z_][A-Za-z0-9_]*)\b", body)
    if len(objectives) > 1:
        raise SetupError(f"model has multiple objectives: {model_path}")
    if not objectives:
        return "satisfy", None
    kind, var = objectives[0]
    return kind, var


def parse_stats(stderr: str) -> tuple[dict[str, object] | None, str | None]:
    """Strictly parse the one mandatory stats line.

    Returns (stats, error_kind).  Error kinds are
    ``missing_stats``, ``multiple_stats`` or ``malformed_stats``.
    """
    lines = [line.strip() for line in stderr.splitlines()
             if line.strip().startswith("leanfzn: stats:")]
    if not lines:
        return None, "missing_stats"
    if len(lines) > 1:
        return None, "multiple_stats"
    body = lines[0][len("leanfzn: stats:"):].strip()
    token_re = re.compile(
        r'([A-Za-z_][A-Za-z0-9_]*)=("(?:[^"\\]|\\.)*"|\S+)')
    values: dict[str, str] = {}
    pos = 0
    for m in token_re.finditer(body):
        # Anything outside a key=value token is malformed; in particular a
        # truncated field must not silently disappear.
        if body[pos:m.start()].strip():
            return None, "malformed_stats"
        key, raw = m.group(1), m.group(2)
        if key in values:
            return None, "malformed_stats"
        if raw.startswith('"') and raw.endswith('"'):
            raw = raw[1:-1]
        values[key] = raw
        pos = m.end()
    if body[pos:].strip():
        return None, "malformed_stats"
    stats: dict[str, object] = {}
    for key in MANDATORY_STATS:
        if key not in values:
            return None, "malformed_stats"
        raw = values[key]
        if not re.fullmatch(r"\d+", raw):
            return None, "malformed_stats"
        stats[key] = int(raw)
    for key in ("complete", "gaveUp"):
        if stats[key] not in (0, 1):  # type: ignore[operator]
            return None, "malformed_stats"
    stats["cause"] = values.get("cause", "")
    stats["seeds"] = values.get("seeds", "")
    return stats, None


def parse_stream(stdout: str, mode: str,
                 objective_var: str | None) -> dict[str, object]:
    """Split stdout into complete solution blocks and terminal markers.

    Raises ``ValueError`` for malformed/truncated streams.  The objective is
    read from the declared objective variable in each block, never from the
    last scalar assignment.
    """
    lines = stdout.splitlines()
    blocks: list[str] = []
    cur: list[str] = []
    markers: list[str] = []
    for raw in lines:
        t = raw.strip()
        if t == "----------":
            if any(line.strip() for line in cur):
                blocks.append("\n".join(cur))
            else:
                raise ValueError("empty solution block")
            cur = []
            continue
        if t in KNOWN_MARKERS:
            markers.append(t)
            continue
        if t.startswith("=====") and t.endswith("====="):
            raise ValueError(f"unknown status marker {t!r}")
        cur.append(raw)
    if any(line.strip() for line in cur):
        raise ValueError("unterminated solution block")
    if len(markers) != len(set(markers)):
        raise ValueError("duplicate terminal marker")
    terminal = [m for m in markers if m in {
        MARKER_UNSAT, MARKER_OPTIMUM, MARKER_UNKNOWN,
        MARKER_UNBOUNDED, MARKER_UNSAT_OR_UNBOUNDED, MARKER_ERROR}]
    if len(terminal) > 1:
        raise ValueError(f"conflicting terminal markers: {terminal}")
    if MARKER_UNSAT in markers:
        kind = "unsat"
    elif MARKER_OPTIMUM in markers:
        kind = "optimal"
    elif MARKER_UNKNOWN in markers:
        kind = "unknown"
    elif MARKER_UNBOUNDED in markers:
        kind = "unbounded"
    elif MARKER_UNSAT_OR_UNBOUNDED in markers:
        kind = "unsat_or_unbounded"
    elif MARKER_ERROR in markers:
        kind = "error_marker"
    else:
        kind = None

    if mode == "satisfy":
        if kind == "optimal":
            raise ValueError("satisfy run emitted an optimum marker")
        if len(blocks) > 1:
            raise ValueError("satisfy run emitted multiple solutions")
        objectives: list[int | None] = [None] * len(blocks)
    else:
        if kind in {"unsat", "unknown", "unbounded", "unsat_or_unbounded"}:
            objectives = [None] * len(blocks)
        else:
            objectives = []
            pat = re.compile(
                r"^\s*" + re.escape(objective_var or "") +
                r"\s*=\s*(-?\d+)\s*;\s*$")
            for block in blocks:
                found = None
                for line in block.splitlines():
                    m = pat.match(line)
                    if m:
                        found = int(m.group(1))
                        break
                if found is None:
                    raise ValueError(
                        f"solution block has no assignment for objective "
                        f"variable {objective_var!r}")
                objectives.append(found)
    return {
        "blocks": blocks,
        "objectives": objectives,
        "markers": markers,
        "marker_kind": kind,
        "solutions": len(blocks),
        "objective": objectives[-1] if objectives else None,
    }


def classify(stats_error: str | None, stream: dict[str, object] | None,
             stream_error: str | None, rc: int, timed_out: bool,
             mode: str) -> str:
    if timed_out or rc in (124, 137, -signal.SIGKILL):
        return "timeout"
    if stream_error:
        return "malformed_output"
    if stats_error:
        return stats_error
    assert stream is not None
    kind = stream["marker_kind"]
    solutions = int(stream["solutions"])
    if kind == "unsat":
        return "unsat" if rc == 1 and solutions == 0 else "inconsistent_exit"
    if kind == "optimal":
        if mode == "satisfy":
            return "inconsistent_output"
        return "optimal" if rc == 0 and solutions > 0 else "inconsistent_exit"
    if kind in {"unknown", "unbounded", "unsat_or_unbounded", "error_marker"}:
        return f"unexpected_{kind}"
    if rc == 0:
        if mode != "satisfy":
            return "inconsistent_output" if solutions != 0 else "empty"
        return "sat" if solutions == 1 else "empty"
    if rc == 4:
        return "incomplete"
    if rc == 3:
        return "unsupported"
    if rc == 1:
        return "inconsistent_exit"
    if rc == 2:
        return "error_rc2"
    return f"error_rc{rc}"


def run_one(binary: str, model: str, limit: int, cap: int,
            flags: list[str], core: int, no_taskset: bool,
            root: Path, mode: str, objective_var: str | None) -> dict:
    cmd = ["timeout", "--signal=KILL", str(cap)]
    if not no_taskset:
        cmd += ["taskset", "-c", str(core)]
    cmd += [binary, "solve", model, "--stats",
            f"--conflict-limit={limit}"] + flags
    start = time.perf_counter()
    timed_out = False
    rc: int | None = None
    stderr = ""
    stdout = ""
    exec_error = None
    try:
        p = subprocess.run(cmd, cwd=root, stdout=subprocess.PIPE,
                           stderr=subprocess.PIPE, text=True,
                           encoding="utf-8", errors="replace",
                           timeout=cap + 30)
        rc = p.returncode
        stdout, stderr = p.stdout, p.stderr
        # With --signal=KILL, GNU timeout can itself die from SIGKILL.
        # subprocess reports that directly as -9, rather than shell status 137.
        timed_out = rc in (124, 137, -signal.SIGKILL)
    except subprocess.TimeoutExpired as exc:
        timed_out = True
        rc = 124
        stdout = (exc.stdout or "") if isinstance(exc.stdout, str) else ""
        stderr = (exc.stderr or "") if isinstance(exc.stderr, str) else ""
    except OSError as exc:
        exec_error = f"cannot execute {binary}: {exc}"
    wall = time.perf_counter() - start

    if exec_error:
        return {"stats": None, "stats_error": "exec_error", "outcome": "exec_error",
                "objective": None, "solutions": 0, "wall": wall, "rc": rc,
                "cause": "", "stream_error": exec_error, "blocks": [],
                "objectives": [], "markers": [], "exec_error": exec_error,
                "timed_out": False, "complete": None, "gave_up": None,
                "incumbents": None}

    stats, stats_error = parse_stats(stderr)
    stream = None
    stream_error = None
    try:
        stream = parse_stream(stdout, mode, objective_var)
    except ValueError as exc:
        stream_error = str(exc)
    outcome = classify(stats_error, stream, stream_error, int(rc or 0),
                       timed_out, mode)
    complete = stats.get("complete") if stats else None
    gave_up = stats.get("gaveUp") if stats else None
    incumbents = stats.get("incumbents") if stats else None
    return {
        "stats": stats,
        "stats_error": stats_error,
        "outcome": outcome,
        "objective": (stream or {}).get("objective"),
        "solutions": int((stream or {}).get("solutions", 0)),
        "wall": wall,
        "rc": rc,
        "cause": (stats or {}).get("cause", ""),
        "stream_error": stream_error,
        "blocks": (stream or {}).get("blocks", []),
        "objectives": (stream or {}).get("objectives", []),
        "markers": (stream or {}).get("markers", []),
        "exec_error": None,
        "complete": complete,
        "gave_up": gave_up,
        "incumbents": incumbents,
        "timed_out": timed_out,
    }


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def _safe_name(name: str) -> str:
    out = re.sub(r"[^A-Za-z0-9_.-]+", "_", name)
    return out[:80] or "case"


def check_witnesses(case_id: str, model_path: Path, streams: dict[str, list[str]],
                    checkers: list[tuple[str, str]], outdir: Path,
                    root: Path, cap: int) -> tuple[list[dict[str, str]], int]:
    """Check every emitted solution block with every distinct checker.

    ``streams`` maps side -> solution blocks.  Each file contains all blocks
    for that side, separated by ``----------``; ``leanfzn check`` verifies all
    of them and returns non-zero on the first rejected one.  Returns
    (failures, number of solution witnesses covered).
    """
    failures: list[dict[str, str]] = []
    checked = 0
    distinct: list[tuple[str, str]] = []
    seen: set[str] = set()
    for side, binary in checkers:
        key = os.path.realpath(binary)
        if key not in seen:
            seen.add(key)
            distinct.append((side, binary))
    for side, blocks in streams.items():
        if not blocks:
            continue
        case_dir = outdir / "cases" / _safe_name(case_id)
        case_dir.mkdir(parents=True, exist_ok=True)
        sol_path = case_dir / f"{side}.solutions.txt"
        text = "\n----------\n".join(b.rstrip("\n") for b in blocks)
        sol_path.write_text(text + "\n----------\n", encoding="utf-8")
        for checker_side, checker in distinct:
            cmd = [checker, "check", str(model_path), str(sol_path)]
            try:
                p = subprocess.run(
                    cmd, cwd=root, stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE, text=True, encoding="utf-8",
                    errors="replace", timeout=cap)
            except subprocess.TimeoutExpired:
                failures.append({
                    "class": "checker_timeout",
                    "detail": f"{side} witnesses: checker {checker_side} timed "
                              f"out after {cap}s",
                })
                continue
            except OSError as exc:
                failures.append({
                    "class": "checker_error",
                    "detail": f"{side} witnesses: cannot execute checker "
                              f"{checker_side}: {exc}",
                })
                continue
            out = (p.stdout or "").strip()
            last = out.splitlines()[-1] if out.splitlines() else ""
            all_m = re.fullmatch(r"all (\d+) solutions accepted", last)
            single = re.fullmatch(r"solution accepted", last) is not None
            accepted = p.returncode == 0 and (
                (single and len(blocks) == 1) or
                (all_m is not None and int(all_m.group(1)) == len(blocks)))
            if not accepted:
                failures.append({
                    "class": "rejected_witness",
                    "detail": f"{side} witnesses rejected by checker "
                              f"{checker_side} (rc={p.returncode}): "
                              f"{(p.stdout or p.stderr or '<no output>').strip()[:300]}",
                })
        checked += len(blocks)
    return failures, checked


def evaluate_case(spec: CaseSpec, kind: str, objective_var: str | None,
                  a: dict, b: dict, same_binary: bool,
                  model_path: Path, checkers: list[tuple[str, str]],
                  outdir: Path, root: Path, cap: int) -> dict:
    failures: list[dict[str, str]] = []

    def fail(cls: str, detail: str) -> None:
        failures.append({"class": cls, "detail": detail})

    for side, r in (("a", a), ("b", b)):
        if r["exec_error"]:
            fail("unreadable_binary", f"side {side}: {r['exec_error']}")
        if r["timed_out"] or r["outcome"] == "timeout":
            fail("timeout", f"side {side} hit the external {cap}s cap; "
                            f"timeout is never a pass")
        if r["stats_error"]:
            fail(str(r["stats_error"]),
                 f"side {side}: {r['stats_error']} (stats line is mandatory)")
        if r["stream_error"]:
            fail("malformed_output", f"side {side}: {r['stream_error']}")
        if r["outcome"] in {"exec_error", "malformed_output"}:
            continue

    if not failures:
        if a["outcome"] != b["outcome"]:
            fail("unexpected_outcome",
                 f"terminal outcomes differ: a={a['outcome']} b={b['outcome']}")
        if a["rc"] != b["rc"]:
            fail("unexpected_outcome",
                 f"exit classes differ: a={a['rc']} b={b['rc']}")
        if a["solutions"] != b["solutions"]:
            fail("missing_solution",
                 f"solution counts differ: a={a['solutions']} "
                 f"b={b['solutions']}")

    expected = spec.expected_class
    if expected is not None:
        want = {"sat": "sat", "unsat": "unsat", "optimal": "optimal",
                "incomplete": "incomplete"}[expected]
        for side, r in (("a", a), ("b", b)):
            if r["outcome"] != want:
                fail("unexpected_outcome",
                     f"side {side} outcome {r['outcome']!r} != expected "
                     f"{want!r}")
    else:
        for side, r in (("a", a), ("b", b)):
            if r["outcome"] == "incomplete":
                fail("unexpected_outcome",
                     f"side {side} is incomplete but the cohort declares no "
                     f"expectation; use --cohort-tsv to record it")

    # Completion metadata must agree with the terminal class.
    for side, r in (("a", a), ("b", b)):
        outcome = r["outcome"]
        complete = r.get("complete")
        gave_up = r.get("gave_up")
        incumbents = r.get("incumbents")
        if complete is None or gave_up is None:
            continue
        if expected == "incomplete":
            if complete != 0 or gave_up != 1:
                fail("unexpected_outcome",
                     f"side {side}: incomplete requires complete=0,gaveUp=1 "
                     f"(got complete={complete},gaveUp={gave_up})")
        elif expected in {"sat", "unsat", "optimal"}:
            if complete != 1 or gave_up != 0:
                fail("unexpected_outcome",
                     f"side {side}: {expected} requires complete=1,gaveUp=0 "
                     f"(got complete={complete},gaveUp={gave_up})")
        if incumbents is not None:
            if kind == "satisfy":
                if incumbents != 0:
                    fail("malformed_stats",
                         f"side {side}: satisfy run reports "
                         f"incumbents={incumbents}")
            elif incumbents != r["solutions"]:
                fail("malformed_stats",
                     f"side {side}: incumbents={incumbents} but "
                     f"{r['solutions']} solution blocks")

    # Objective metadata is decoded from the declared variable, never from
    # the last scalar assignment.
    if kind == "satisfy":
        for side, r in (("a", a), ("b", b)):
            if r["objective"] is not None:
                fail("objective_mismatch",
                     f"side {side}: satisfy run has an objective value")
    else:
        for side, r in (("a", a), ("b", b)):
            if r["solutions"] and r["objective"] is None:
                fail("malformed_output",
                     f"side {side}: no value for declared objective variable "
                     f"{objective_var!r}")
        if spec.known_answer is not None:
            for side, r in (("a", a), ("b", b)):
                if r["objective"] != spec.known_answer:
                    fail("wrong_objective",
                         f"side {side}: objective {r['objective']} != known "
                         f"answer {spec.known_answer}")
        if spec.exact_counters or same_binary:
            if a["objective"] != b["objective"]:
                fail("objective_mismatch",
                     f"objectives differ: a={a['objective']} "
                     f"b={b['objective']}")

    # Counters: mandatory presence was checked above; equality is demanded
    # only for declared deterministic cases or a same-binary identity run.
    diffs: list[str] = []
    if not failures and a["stats"] is not None and b["stats"] is not None:
        for key in ACTION_KEYS + AUX_KEYS:
            av = a["stats"].get(key)
            bv = b["stats"].get(key)
            if av != bv:
                diffs.append(f"{key}:{av}!={bv}")
        if (spec.exact_counters or same_binary) and diffs:
            fail("counter_mismatch",
                 "deterministic counters differ: " + ", ".join(diffs))
    if same_binary and not diffs and a["stats"] is not None and b["stats"] is not None:
        if a["stats"].get("complete") != b["stats"].get("complete") or \
           a["stats"].get("gaveUp") != b["stats"].get("gaveUp"):
            fail("counter_mismatch",
                 "same-binary completion metadata differs")

    # Every emitted witness from both sides is checked against the source
    # model by every distinct checker (baseline and candidate).
    streams = {"a": a["blocks"], "b": b["blocks"]}
    witness_failures, checked = check_witnesses(
        spec.case_id, model_path, streams, checkers, outdir, root, cap)
    failures.extend(witness_failures)

    return {
        "case_id": spec.case_id,
        "case": spec.model,
        "model": spec.model,
        "model_sha256": sha256_file(model_path),
        "mode": kind,
        "objective_var": objective_var,
        "expected_class": spec.expected_class,
        "known_answer": spec.known_answer,
        "known_answer_source": spec.known_answer_source,
        "exact_counters": spec.exact_counters,
        "limit": spec.conflict_limit,
        "a": a,
        "b": b,
        "counter_diffs": diffs,
        "witnesses_checked": checked,
        "failures": failures,
        "passed": not failures,
    }


def setup_error(msg: str) -> int:
    print(f"error: {msg}", file=sys.stderr)
    return 2


def main() -> int:
    args = parse_args()
    root = Path(args.root).resolve()
    if not root.is_dir():
        return setup_error(f"--root is not a directory: {root}")
    for label, path in (("binary A", args.binary_a), ("binary B", args.binary_b),
                        ("checker A", args.checker_a),
                        ("checker B", args.checker_b)):
        p = Path(path)
        if not p.is_file():
            return setup_error(f"{label} not found: {path}")
        if not os.access(path, os.X_OK):
            return setup_error(f"{label} is not executable: {path}")
    for cmd in ("timeout",):
        if shutil.which(cmd) is None:
            return setup_error(f"required command not found: {cmd}")
    if not args.no_taskset and shutil.which("taskset") is None:
        return setup_error("required command not found: taskset "
                           "(or pass --no-taskset)")

    try:
        flags_a = shlex.split(args.flags_a)
        flags_b = shlex.split(args.flags_b)
    except ValueError as exc:
        return setup_error(f"invalid shell-quoted flags: {exc}")
    forbidden = {"--threads", "--portfolio", "--time-limit", "--conflict-limit",
                 "--stats"}
    for side, flags in (("A", flags_a), ("B", flags_b)):
        for flag in flags:
            name = flag.split("=", 1)[0]
            if name in forbidden:
                return setup_error(
                    f"--flags-{side.lower()} contains {name}; fixed_k.py is "
                    f"for deterministic single-worker conflict-limited runs")
    if args.require_equal_flags and flags_a != flags_b:
        return setup_error("--require-equal-flags: side flags differ "
                           f"({flags_a!r} vs {flags_b!r})")

    try:
        if args.cohort_tsv:
            specs = load_cohort_tsv(args.cohort_tsv)
        else:
            models = cases_from(args.cohort or [])
            if not models:
                raise SetupError("cohort contains no cases")
            specs = [CaseSpec(case_id=m, model=m) for m in models]
        # Validate every model and the declared mode before running anything.
        prepared: list[CaseSpec] = []
        for spec in specs:
            model_path = Path(spec.model)
            if not model_path.is_absolute():
                model_path = root / model_path
            if not model_path.is_file():
                raise SetupError(f"missing fixture for case {spec.case_id!r}: "
                                 f"{model_path}")
            kind, objective_var = model_solve(model_path)
            if spec.mode != "auto" and spec.mode != kind:
                raise SetupError(
                    f"case {spec.case_id!r}: declared mode {spec.mode!r} but "
                    f"model solve item is {kind!r}")
            if kind != "satisfy" and objective_var is None:
                raise SetupError(
                    f"case {spec.case_id!r}: optimization model has no "
                    f"declared objective variable")
            prepared.append(replace(spec, mode=kind))
        specs = prepared
    except SetupError as exc:
        return setup_error(str(exc))

    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    outdir = Path(args.out) if args.out else (root / "tmp/performance/fixed_k" / stamp)
    outdir.mkdir(parents=True, exist_ok=True)
    json_path = Path(args.json) if args.json else outdir / "fixed_k.json"

    same_binary = (os.path.realpath(args.binary_a) == os.path.realpath(args.binary_b)
                   and flags_a == flags_b)
    checkers = [("a", args.checker_a), ("b", args.checker_b)]
    cases_json: list[dict] = []
    rows: list[dict] = []
    failed_cases = 0
    counter_mismatches = 0
    witness_total = 0

    print(f"binary A: {args.binary_a} {flags_a}")
    print(f"binary B: {args.binary_b} {flags_b}")
    print(f"limit: {args.limit}  cases: {len(specs)}  cap: {args.cap}s  "
          f"same-binary: {same_binary}")
    print(f"out: {outdir}")

    lockf = None
    try:
        lock_path = Path(args.lock)
        lock_path.parent.mkdir(parents=True, exist_ok=True)
        lockf = lock_path.open("w")
        fcntl.flock(lockf, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except (OSError, BlockingIOError) as exc:
        return setup_error(f"cannot acquire measurement lock {args.lock}: {exc}")

    try:
        for i, spec in enumerate(specs, 1):
            model_path = Path(spec.model)
            if not model_path.is_absolute():
                model_path = root / model_path
            kind, objective_var = model_solve(model_path)
            limit = spec.conflict_limit or args.limit
            a = run_one(args.binary_a, str(model_path), limit, args.cap,
                        flags_a, args.core, args.no_taskset, root, kind,
                        objective_var)
            b = run_one(args.binary_b, str(model_path), limit, args.cap,
                        flags_b, args.core, args.no_taskset, root, kind,
                        objective_var)
            row_case = evaluate_case(
                spec, kind, objective_var, a, b, same_binary, model_path,
                checkers, outdir, root, args.cap)
            row_case["limit"] = limit
            cases_json.append(row_case)
            witness_total += row_case["witnesses_checked"]
            passed = row_case["passed"]
            if not passed:
                failed_cases += 1
            if row_case["counter_diffs"]:
                counter_mismatches += 1
            row = {
                "case": spec.model,
                "outcome_a": a["outcome"],
                "outcome_b": b["outcome"],
                "wall_a": a["wall"],
                "wall_b": b["wall"],
                "ratio": (b["wall"] / a["wall"]) if a["wall"] > 0 else float("inf"),
                "equal": passed and not row_case["counter_diffs"],
                "diffs": ",".join(row_case["counter_diffs"]),
                "objective_a": "-" if a["objective"] is None else a["objective"],
                "objective_b": "-" if b["objective"] is None else b["objective"],
                "solutions_a": a["solutions"],
                "solutions_b": b["solutions"],
                "case_id": spec.case_id,
                "mode": kind,
                "expected_class": spec.expected_class or "-",
                "known_answer": "-" if spec.known_answer is None else spec.known_answer,
                "exact_counters": spec.exact_counters,
                "objective_var": objective_var or "-",
                "exit_a": a["rc"],
                "exit_b": b["rc"],
                "witnesses_checked": row_case["witnesses_checked"],
                "failures": ";".join(
                    f"{f['class']}: {f['detail']}" for f in row_case["failures"]),
            }
            rows.append(row)
            if not args.quiet:
                tag = "PASS" if passed else "FAIL"
                short = Path(spec.model).name[:44]
                detail = ""
                if row_case["failures"]:
                    detail = " | " + row_case["failures"][0]["class"]
                elif row_case["counter_diffs"]:
                    detail = " | differing=" + ",".join(row_case["counter_diffs"])
                print(f"[{i:3d}/{len(specs)}] {short:46s} {tag:4s} "
                      f"{a['outcome']:>12s}/{b['outcome']:<12s} "
                      f"wall {a['wall']:.3f}/{b['wall']:.3f} "
                      f"x{row['ratio']:.3f}{detail}")
    finally:
        if lockf is not None:
            lockf.close()

    tsv = outdir / "fixed_k.tsv"
    with tsv.open("w", encoding="utf-8") as f:
        f.write("\t".join([
            "case", "outcome_a", "outcome_b", "wall_a", "wall_b",
            "ratio_b_over_a", "counters_equal", "differing", "objective_a",
            "objective_b", "solutions_a", "solutions_b", "case_id", "mode",
            "expected_class", "known_answer", "exact_counters",
            "objective_var", "exit_a", "exit_b", "witnesses_checked",
            "failures",
        ]) + "\n")
        for r in rows:
            f.write("\t".join(str(r[k]) for k in [
                "case", "outcome_a", "outcome_b", "wall_a", "wall_b",
                "ratio", "equal", "diffs", "objective_a", "objective_b",
                "solutions_a", "solutions_b", "case_id", "mode",
                "expected_class", "known_answer", "exact_counters",
                "objective_var", "exit_a", "exit_b", "witnesses_checked",
                "failures"]) + "\n")

    status = "pass" if failed_cases == 0 else "fail"
    report = {
        "schema_version": 1,
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "status": status,
        "binary_a": args.binary_a,
        "binary_b": args.binary_b,
        "sha256_a": sha256_file(Path(args.binary_a)),
        "sha256_b": sha256_file(Path(args.binary_b)),
        "checker_a": args.checker_a,
        "checker_b": args.checker_b,
        "flags_a": flags_a,
        "flags_b": flags_b,
        "limit": args.limit,
        "cap": args.cap,
        "same_binary": same_binary,
        "cases": cases_json,
        "summary": {
            "cases": len(cases_json),
            "passed": len(cases_json) - failed_cases,
            "failed": failed_cases,
            "counter_mismatch_cases": counter_mismatches,
            "witnesses_checked": witness_total,
            "timeouts": sum(
                1 for c in cases_json
                for side in ("a", "b") if side in c and
                c[side].get("outcome") == "timeout"),
        },
    }
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(report, indent=2, sort_keys=False) + "\n",
                         encoding="utf-8")

    same = len(rows) - failed_cases
    print(f"\n{same}/{len(rows)} cases passed"
          f"{' (PASS)' if failed_cases == 0 else ' (FAILURES FOUND)'}")
    print(f"witnesses checked: {witness_total}")
    print(f"results: {tsv}")
    print(f"json: {json_path}")
    return 0 if failed_cases == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
