#!/usr/bin/env python3
"""Independent oracle checks over a ``strategy_matrix.py`` results directory.

Usage:
  python3 audits/oracle_check.py RESULTS_DIR [--binary PATH] [--targets PATH]
                                            [--json OUT]

This tool is development-only.  It imports only the Python standard library
(plus the sibling ``strategy_matrix`` module for its results-directory
format), is never imported by Lean code, and never decides a solver result.

Three independent oracles run over the directory:

* witness   -- every complete solution block in every ``.stdout`` plus every
               captured ``.last-solution.txt`` is re-checked against the
               original model with ``leanfzn check``.  A rejected witness is a
               hard failure.
* challenge -- ``matrix.tsv`` claims are joined against the official
               MiniZinc Challenge result CSVs by ``(year, problem, instance)``
               and against ``strategy_targets.tsv``.  The official statuses are
               ``S`` (solution found), ``C`` (search complete), and ``SC``
               (both); ``C`` without ``S`` therefore certifies that no solution
               exists.  A claimed UNSAT that contradicts a solved result, a
               claimed solution contradicted by a complete search without a
               solution, a proved optimum that differs from an ``SC``
               objective, and an incumbent better than a complete objective or
               the published target are failures.
* cross-run -- claims made by different runs for the same model are compared.
               UNSAT versus a solution, two different proved optima, and an
               objective better than a proved optimum or target are failures.

``unsupported`` (exit 3), ``unknown`` (exit 4), ``timeout`` and rows without a
printed solution are observations, not claims: they are reported and never
counted as agreement.  A missing or partial results directory is reported
without a traceback.

Exit 0 only when all checks pass; exit 1 on any failed or missing claim.
"""

from __future__ import annotations

import argparse
import csv
import json
import os
import re
import shutil
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(HERE))

import strategy_matrix as sm  # noqa: E402  (sibling tool, not a package)

CHALLENGE_DIR = ROOT / "minizinc-challenge"
CHALLENGE_YEARS = (2025, 2026)
# Official MiniZinc Challenge status legend: S = solution found,
# C = search complete, SC = solution found and search complete.
# In particular C alone means an exhaustive search found no solution.
SAT_STATUSES = {"S", "SC"}
COMPLETE_WITHOUT_SOLUTION_STATUSES = {"C", "UNK"}


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("results_dir", help="strategy_matrix results directory")
    p.add_argument("--binary", default=str(sm.DEFAULT_BIN),
                   help="leanfzn binary used for witness checks")
    p.add_argument("--targets", default=str(sm.DEFAULT_TARGETS),
                   help="strategy_targets.tsv with file -> kind/objective")
    p.add_argument("--json", default=None,
                   help="machine-readable report path "
                        "(default RESULTS_DIR/oracle_report.json)")
    return p.parse_args()


# ---------------------------------------------------------------------------
# Small parsers
# ---------------------------------------------------------------------------

def parse_int(value: object) -> int | None:
    if value is None:
        return None
    text = str(value).strip()
    if not text or text == "-":
        return None
    try:
        return int(text)
    except ValueError:
        return None


def better(kind: str | None, value: int, bound: int) -> bool:
    """True when ``value`` is strictly better than ``bound`` for ``kind``."""
    if kind == "MAX":
        return value > bound
    if kind == "MIN":
        return value < bound
    return False


def split_blocks(text: str) -> list[list[str]]:
    """Return complete solution blocks, each terminated by ``----------``.

    A block cut off by a timeout or a killed process has no closing separator
    and is therefore not a solution claim.  ``==========`` completion markers
    are not part of a block.
    """
    blocks: list[list[str]] = []
    current: list[str] = []
    for line in text.splitlines():
        stripped = line.strip()
        if stripped == "----------":
            block = [ln for ln in current if ln.strip()]
            if block:
                blocks.append(block)
            current = []
        elif stripped == "==========":
            current = []
        else:
            current.append(line)
    return blocks


def parse_solution_file(path: Path) -> list[str]:
    try:
        text = path.read_text(errors="replace")
    except OSError:
        return []
    return [ln for ln in text.splitlines()
            if ln.strip() not in ("", "----------", "==========")]


def read_text(path: Path | None) -> str:
    if path is None:
        return ""
    try:
        return path.read_text(errors="replace")
    except OSError:
        return ""


# ---------------------------------------------------------------------------
# Results-directory layout
# ---------------------------------------------------------------------------

def config_tag(config: str) -> str:
    return config.replace("+", "_").replace("=", "-")


def read_matrix(results: Path) -> list[dict]:
    path = results / "matrix.tsv"
    rows: list[dict] = []
    counters: dict[str, int] = {}
    with path.open(encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f, delimiter="\t")
        for raw in reader:
            row = dict(raw)
            config = row.get("config", "")
            counters[config] = counters.get(config, 0) + 1
            row["_index"] = counters[config]
            rows.append(row)
    return rows


def find_artifacts(results: Path, row: dict) -> tuple[Path | None, Path | None]:
    """Locate the per-run stdout/last-solution pair for a matrix row.

    The label is reconstructed exactly as ``strategy_matrix.py`` builds it:
    ``<config-tag>__<model-stem>__<index:03d>``.  A unique glob fallback keeps
    partially renamed directories usable; ambiguity is reported as missing.
    """
    config = config_tag(row.get("config", ""))
    stem = Path(row.get("file", "")).stem
    base = results / f"{config}__{stem}__{row['_index']:03d}"
    stdout = Path(str(base) + ".stdout")
    if not stdout.exists():
        matches = sorted(results.glob(f"{config}__{stem}__*.stdout"))
        stdout = matches[0] if len(matches) == 1 else None
    if stdout is None or not stdout.exists():
        return None, None
    last = stdout.with_name(stdout.name[:-len(".stdout")] +
                            ".last-solution.txt")
    return stdout, last if last.exists() else None


def load_challenge_index() -> tuple[dict, list[str]]:
    index: dict[tuple[int, str, str], list[dict]] = {}
    missing: list[str] = []
    for year in CHALLENGE_YEARS:
        path = CHALLENGE_DIR / f"challengeResults{year}.csv"
        if not path.exists():
            missing.append(str(path))
            continue
        with path.open(encoding="utf-8", newline="") as f:
            for row in csv.DictReader(f):
                instance = row.get("instance", "").strip()
                if instance.endswith(".fzn"):
                    instance = instance[:-len(".fzn")]
                key = (year, row.get("problem", "").strip(), instance)
                index.setdefault(key, []).append(row)
    return index, missing


def challenge_key(model: str) -> tuple[int, str, str] | None:
    m = re.search(
        r"(?:^|/)minizinc-challenge/(\d{4})fzn/([^/]+)/([^/]+)\.fzn$",
        str(model))
    if not m:
        return None
    return int(m.group(1)), m.group(2), m.group(3)


def model_kind(model: str, challenge_rows: list[dict],
               target: tuple[str | None, str | None] | None) -> str | None:
    kinds = [r.get("problem_kind", "").strip() for r in challenge_rows]
    for kind in ("MIN", "MAX"):
        if kind in kinds:
            return kind
    if target and target[0] in ("MIN", "MAX"):
        return target[0]
    path = Path(model)
    if not path.is_absolute():
        path = ROOT / path
    _, kind = sm.model_info(path)
    return kind


# ---------------------------------------------------------------------------
# Witness oracle
# ---------------------------------------------------------------------------

def safe_tag(text: str) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]+", "_", text)[:180]


def first_check_cores() -> str:
    try:
        cpus = sorted(os.sched_getaffinity(0))
    except (AttributeError, OSError):
        cpus = []
    return str(cpus[0]) if cpus else "0"


def run_witness_oracle(results: Path, rows: list[dict], records: list[dict],
                       binary: Path, failures: list[dict]) -> dict:
    tmpdir = Path(tempfile.mkdtemp(prefix="oracle-witness-", dir=str(results)))
    faildir = results / "oracle_failures"
    cores = first_check_cores()
    checked = accepted = rejected = 0
    unchecked_rows = 0
    missing_artifacts: list[dict] = []

    def check(model: str, block: list[str], tag: str) -> None:
        nonlocal checked, accepted, rejected
        out = tmpdir / (safe_tag(tag) + ".solution.txt")
        verdict = sm.check_solution(str(binary), model, block, out, cores)
        checked += 1
        if verdict == "yes":
            accepted += 1
            return
        rejected += 1
        faildir.mkdir(parents=True, exist_ok=True)
        kept = faildir / (safe_tag(tag) + ".solution.txt")
        kept.write_text("\n".join(block) + "\n----------\n", encoding="utf-8")
        failures.append({
            "oracle": "witness",
            "kind": "rejected-witness",
            "file": model,
            "config": None,
            "artifact": tag,
            "solution_copy": str(kept),
            "verdict": verdict,
        })

    try:
        for rec in records:
            row = rec["row"]
            blocks = rec["blocks"]
            last_block = rec["last_block"]
            if not blocks and not last_block:
                unchecked_rows += 1
                expected = parse_int(row.get("n_solutions")) or 0
                if expected > 0:
                    missing_artifacts.append({
                        "file": row.get("file"),
                        "config": row.get("config"),
                        "row": row["_index"],
                        "reason": "n_solutions>0 but no stdout block or "
                                  ".last-solution.txt",
                    })
                continue
            tag_base = (f"{config_tag(row.get('config', ''))}"
                        f"__{Path(row.get('file', '')).stem}"
                        f"__{row['_index']:03d}")
            seen: set[tuple[str, ...]] = set()
            for i, block in enumerate(blocks):
                key = tuple(block)
                if key in seen:
                    continue
                seen.add(key)
                check(row.get("file", ""), block, f"{tag_base}__stdout{i}")
            if last_block:
                check(row.get("file", ""), last_block,
                      f"{tag_base}__last_solution")
    finally:
        shutil.rmtree(tmpdir, ignore_errors=True)

    return {
        "rows": len(rows),
        "checked": checked,
        "accepted": accepted,
        "rejected": rejected,
        "unchecked": unchecked_rows,
        "missing_artifacts": missing_artifacts,
    }


# ---------------------------------------------------------------------------
# Challenge oracle
# ---------------------------------------------------------------------------

def run_challenge_oracle(rows: list[dict], records: list[dict],
                         targets: dict[str, tuple[str | None, str | None]],
                         failures: list[dict]) -> dict:
    index, missing_csv = load_challenge_index()
    matched = unmatched = claims = 0
    unsat_claims = optimum_claims = incumbent_claims = 0
    warnings: list[str] = []
    seen_keys: set[tuple[int, str, str]] = set()

    if missing_csv:
        warnings.append("missing challenge CSV(s): " + ", ".join(missing_csv))

    for rec in records:
        row = rec["row"]
        file = row.get("file", "")
        key = challenge_key(file)
        target = targets.get(file)
        best = rec["best"]
        outcome = row.get("outcome", "")
        if key is None:
            unmatched += 1
            continue
        seen_keys.add(key)
        if key not in index:
            unmatched += 1
            rec["challenge_matched"] = False
            continue
        matched += 1
        rec["challenge_matched"] = True
        challenge_rows = index[key]
        kind = model_kind(file, challenge_rows, target)

        claim_unsat = rec["unsat"]
        if (not claim_unsat and outcome == "proved" and best is None
                and not rec["stdout_text"] and not rec["blocks"]):
            claim_unsat = True
        claim_opt = outcome == "proved" and best is not None
        claim_incumbent = (best is not None and not claim_opt
                           and (rec["blocks"] or
                                (parse_int(row.get("n_solutions")) or 0) > 0))

        statuses = {r.get("status", "").strip() for r in challenge_rows}
        if claim_unsat:
            claims += 1
            unsat_claims += 1
            solved = statuses & SAT_STATUSES
            if solved:
                failures.append({
                    "oracle": "challenge",
                    "kind": "proved-unsat-but-solved",
                    "file": file,
                    "config": row.get("config"),
                    "row": row["_index"],
                    "detail": "claimed UNSAT but CSV statuses "
                              f"{sorted(solved)} for {key}",
                })

        claim_solution = (
            bool(rec["blocks"]) or bool(rec["last_block"])
            or (parse_int(row.get("n_solutions")) or 0) > 0
            or claim_opt)
        if (claim_solution and statuses
                and statuses <= COMPLETE_WITHOUT_SOLUTION_STATUSES
                and "C" in statuses):
            failures.append({
                "oracle": "challenge",
                "kind": "solution-but-complete-unsat",
                "file": file,
                "config": row.get("config"),
                "row": row["_index"],
                "detail": "claimed solution but CSV statuses "
                          f"{sorted(statuses)} include a complete search "
                          f"without a reported solution for {key}",
            })

        if best is None:
            continue
        if not (claim_opt or claim_incumbent):
            # No printed solution and no proved optimum: an unsupported,
            # unknown or plain timeout row is not an objective claim.
            continue
        if kind is None:
            warnings.append(
                f"objective claim without MIN/MAX kind: {file}")
            continue
        if claim_opt:
            claims += 1
            optimum_claims += 1
        elif claim_incumbent:
            claims += 1
            incumbent_claims += 1

        complete = []
        for r in challenge_rows:
            if r.get("status", "").strip() != "SC":
                continue
            value = parse_int(r.get("objective"))
            if value is not None:
                complete.append(value)
        complete = sorted(set(complete))

        if claim_opt and complete:
            for value in complete:
                if best != value:
                    failures.append({
                        "oracle": "challenge",
                        "kind": "optimum-differs-from-complete",
                        "file": file,
                        "config": row.get("config"),
                        "row": row["_index"],
                        "detail": f"claimed optimum {best} ({kind}) but "
                                  f"SC objective is {value} for {key}",
                    })

        for value in complete:
            if better(kind, best, value):
                failures.append({
                    "oracle": "challenge",
                    "kind": "incumbent-better-than-complete",
                    "file": file,
                    "config": row.get("config"),
                    "row": row["_index"],
                    "detail": f"incumbent {best} ({kind}) is better than "
                              f"SC objective {value} for {key}",
                })

        if target and target[1] is not None:
            tkind = target[0] if target[0] in ("MIN", "MAX") else kind
            tvalue = parse_int(target[1])
            if tvalue is not None and better(tkind, best, tvalue):
                failures.append({
                    "oracle": "challenge",
                    "kind": "objective-better-than-target",
                    "file": file,
                    "config": row.get("config"),
                    "row": row["_index"],
                    "detail": f"objective {best} ({tkind}) is better than "
                              f"target {tvalue}",
                })

    return {
        "challenge_csv_missing": missing_csv,
        "models_matched": matched,
        "models_unmatched": unmatched,
        "distinct_models_matched": len(seen_keys),
        "claims_checked": claims,
        "unsat_claims": unsat_claims,
        "optimum_claims": optimum_claims,
        "incumbent_claims": incumbent_claims,
        "warnings": warnings,
    }


# ---------------------------------------------------------------------------
# Cross-run oracle
# ---------------------------------------------------------------------------

def row_label(row: dict) -> str:
    return f"{row.get('file')} [{row.get('config')}] row {row['_index']}"


def run_cross_run_oracle(records: list[dict],
                         targets: dict[str, tuple[str | None, str | None]],
                         failures: list[dict]) -> dict:
    groups: dict[str, list[dict]] = {}
    for rec in records:
        groups.setdefault(rec["row"].get("file", ""), []).append(rec)

    checked_groups = 0
    for file, group in groups.items():
        if len(group) < 1:
            continue
        checked_groups += 1
        unsat = [r for r in group if r["claim_unsat"]]
        solved = [r for r in group
                  if r["blocks"] or (parse_int(r["row"].get("n_solutions"))
                                     or 0) > 0]
        if unsat and solved:
            failures.append({
                "oracle": "cross-run",
                "kind": "unsat-versus-solution",
                "file": file,
                "config": None,
                "detail": "UNSAT claim " + row_label(unsat[0]["row"]) +
                          " versus solution " + row_label(solved[0]["row"]),
            })

        proved = [(r, r["best"]) for r in group
                  if r["claim_opt"] and r["best"] is not None]
        values = sorted({v for _, v in proved})
        if len(values) > 1:
            failures.append({
                "oracle": "cross-run",
                "kind": "proved-optima-differ",
                "file": file,
                "config": None,
                "detail": ", ".join(
                    f"{row_label(r['row'])}={v}" for r, v in proved),
            })
        proved_value = values[0] if len(values) == 1 else None

        for rec in group:
            best = rec["best"]
            if best is None:
                continue
            if not (rec["claim_opt"] or rec["blocks"]
                    or (parse_int(rec["row"].get("n_solutions")) or 0) > 0):
                # An unsupported/unknown row with no printed solution is not
                # an objective claim, even if a partial TSV says otherwise.
                continue
            kind = model_kind(file, [], targets.get(file))
            if proved_value is not None and better(kind, best, proved_value):
                failures.append({
                    "oracle": "cross-run",
                    "kind": "objective-better-than-proved-optimum",
                    "file": file,
                    "config": rec["row"].get("config"),
                    "row": rec["row"]["_index"],
                    "detail": f"objective {best} ({kind}) is better than "
                              f"proved optimum {proved_value}",
                })
            target = targets.get(file)
            if target and target[1] is not None:
                tkind = target[0] if target[0] in ("MIN", "MAX") else kind
                tvalue = parse_int(target[1])
                if tvalue is not None and better(tkind, best, tvalue):
                    failures.append({
                        "oracle": "cross-run",
                        "kind": "objective-better-than-target",
                        "file": file,
                        "config": rec["row"].get("config"),
                        "row": rec["row"]["_index"],
                        "detail": f"objective {best} ({tkind}) is better "
                                  f"than target {tvalue}",
                    })

    return {"model_groups": checked_groups}


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------

def build_records(results: Path, rows: list[dict]) -> tuple[list[dict], list[dict]]:
    records: list[dict] = []
    missing: list[dict] = []
    for row in rows:
        stdout_path, last_path = find_artifacts(results, row)
        stdout_text = read_text(stdout_path)
        blocks = split_blocks(stdout_text)
        last_block = parse_solution_file(last_path) if last_path else []
        best = parse_int(row.get("best_objective"))
        outcome = row.get("outcome", "")
        unsat = "UNSATISFIABLE" in stdout_text
        claim_unsat = (unsat or
                       (outcome == "proved" and best is None
                        and not stdout_text and not blocks))
        claim_opt = outcome == "proved" and best is not None
        if stdout_path is None:
            missing.append({
                "file": row.get("file"),
                "config": row.get("config"),
                "row": row["_index"],
                "reason": "stdout missing",
            })
        records.append({
            "row": row,
            "stdout_path": stdout_path,
            "last_path": last_path,
            "stdout_text": stdout_text,
            "blocks": blocks,
            "last_block": last_block,
            "best": best,
            "unsat": unsat,
            "claim_unsat": claim_unsat,
            "claim_opt": claim_opt,
        })
    return records, missing


def write_summary(path: Path, report: dict) -> None:
    w = report["witness"]
    c = report["challenge"]
    x = report["cross_run"]
    lines = [
        f"O3 oracle check: {report['results_dir']}",
        f"binary: {report['binary']}",
        f"verdict: {'PASS' if report['pass'] else 'FAIL'}",
        f"witness: rows={w['rows']} checked={w['checked']} "
        f"accepted={w['accepted']} rejected={w['rejected']} "
        f"unchecked={w['unchecked']}",
        f"challenge: matched={c['models_matched']} "
        f"unmatched={c['models_unmatched']} claims={c['claims_checked']} "
        f"failures={report['counts']['challenge_failures']}",
        f"cross-run: groups={x['model_groups']} "
        f"failures={report['counts']['cross_run_failures']}",
        f"unsupported rows: {report['counts']['unsupported']} "
        f"(observations, never agreement)",
    ]
    for warning in report["warnings"]:
        lines.append(f"warning: {warning}")
    if report["failures"]:
        lines.append(f"failures: {len(report['failures'])}")
        for f in report["failures"]:
            lines.append(f"  - [{f['oracle']}/{f['kind']}] {f.get('file')} "
                         f"{f.get('config') or ''} {f.get('detail', '')}".rstrip())
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    args = parse_args()
    results = Path(args.results_dir)
    binary = Path(args.binary)
    if not binary.is_absolute():
        binary = (ROOT / binary).resolve()
    json_path = Path(args.json) if args.json else results / "oracle_report.json"

    failures: list[dict] = []
    warnings: list[str] = []
    report: dict = {
        "tool": "audits/oracle_check.py",
        "generated_utc": datetime.now(timezone.utc).strftime(
            "%Y-%m-%dT%H:%M:%SZ"),
        "results_dir": str(results),
        "binary": str(binary),
        "pass": False,
    }

    matrix_path = results / "matrix.tsv"
    if not results.exists():
        report.update({"error": f"results directory not found: {results}",
                       "failures": [{"oracle": "setup",
                                     "kind": "missing-results",
                                     "file": str(results)}],
                       "counts": {}, "witness": {}, "challenge": {},
                       "cross_run": {}})
        print(f"oracle-check: FAIL: results directory not found: {results}")
        return 1
    if not matrix_path.exists():
        report.update({"error": f"matrix.tsv not found in {results}",
                       "failures": [{"oracle": "setup",
                                     "kind": "missing-matrix",
                                     "file": str(matrix_path)}],
                       "counts": {}, "witness": {}, "challenge": {},
                       "cross_run": {}})
        print(f"oracle-check: FAIL: {matrix_path} not found")
        return 1
    if not binary.exists():
        print(f"oracle-check: FAIL: binary not found: {binary}",
              file=sys.stderr)
        return 2

    rows = read_matrix(results)
    records, missing = build_records(results, rows)
    targets = sm.load_targets(Path(args.targets))
    if not Path(args.targets).exists():
        warnings.append(f"targets file missing: {args.targets}")

    witness = run_witness_oracle(results, rows, records, binary, failures)
    challenge = run_challenge_oracle(rows, records, targets, failures)
    cross_run = run_cross_run_oracle(records, targets, failures)

    # Deduplicate identical failure records (some checks intentionally overlap).
    unique: list[dict] = []
    seen: set[tuple] = set()
    for f in failures:
        key = (f.get("oracle"), f.get("kind"), f.get("file"),
               f.get("config"), f.get("row"), f.get("detail"))
        if key in seen:
            continue
        seen.add(key)
        unique.append(f)
    failures = unique

    unsupported = sum(1 for r in rows
                      if r.get("outcome") == "unsupported")
    unknown = sum(1 for r in rows if r.get("outcome") == "unknown")
    timeouts = sum(1 for r in rows
                   if r.get("outcome", "").startswith("timeout"))
    counts = {
        "rows": len(rows),
        "unsupported": unsupported,
        "unknown": unknown,
        "timeouts": timeouts,
        "witness_failures": sum(1 for f in failures
                                if f["oracle"] == "witness"),
        "challenge_failures": sum(1 for f in failures
                                  if f["oracle"] == "challenge"),
        "cross_run_failures": sum(1 for f in failures
                                  if f["oracle"] == "cross-run"),
        "missing_artifacts": len(missing) + len(witness["missing_artifacts"]),
    }
    report.update({
        "matrix": str(matrix_path),
        "targets": str(args.targets),
        "witness": witness,
        "challenge": challenge,
        "cross_run": cross_run,
        "counts": counts,
        "missing_artifacts": missing + witness["missing_artifacts"],
        "warnings": warnings + challenge["warnings"],
        "failures": failures,
        "pass": not failures,
    })

    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(report, indent=1, sort_keys=True) + "\n",
                         encoding="utf-8")
    summary_path = results / "oracle_summary.txt"
    write_summary(summary_path, report)
    print(summary_path.read_text(encoding="utf-8"), end="")
    print(f"report: {json_path}")
    return 0 if report["pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
