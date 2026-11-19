#!/usr/bin/env python3
"""Keep the repository minimal: every landed support file must be referenced.

Usage:
    python3 -B audits/check_repo_minimal.py            # audit the checkout
    python3 -B audits/check_repo_minimal.py --tracked-only

Rules
-----
1. Every tracked file under `audits/`, `Tests/` and `specification/` (the
   vendored `specification/minizinc-2.10.1/` review pages excluded) must be
   referenced by something maintained in the repository: a script, a Lake
   target, a Lean `import`, CI, a Python/Lean test, or a maintained Markdown
   document.  A reference is the file's repository-relative path or, for
   scripts and data, its basename.
2. Nothing under `tmp/`, no `*.log` file, and neither `prompt.md` nor
   `plan.md` may be tracked.

The allow-list holds the few deliberate exceptions, each with a one-line
justification.  A file that becomes referenced no longer needs its entry; the
audit reports stale entries so the list cannot rot.

Coordination artifacts (plans, briefs, reports, worktree helpers) never belong
in the repository: they are workspace state, not project state.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

SCANNED_TREES = ("audits", "Tests", "specification")
EXCLUDED_PREFIXES = ("specification/minizinc-2.10.1/",)
EXCLUDED_ROOTS = ("tmp/",)
FORBIDDEN_TRACKED_NAMES = ("prompt.md", "plan.md")

# Extensions whose contents are searched for references.
REFERENCE_SOURCES = {
    ".sh", ".py", ".lean", ".toml", ".yml", ".yaml", ".json", ".md", ".txt",
    ".tsv", ".fzn", ".mzn", ".csv", ".cfg", ".in", ".bzl",
}

# <path>: <one-line justification>
ALLOW_LIST = {
    "Tests/README.md":
        "documented map of the test tree; linked from README.md and audits/README.md",
    "Tests/Fixtures/Solver/min_linear_ne.fzn":
        "shared regression model read by the Lean engine and compiler suites",
}


def tracked_files() -> list[str]:
    out = subprocess.run(["git", "ls-files"], cwd=ROOT, text=True,
                         capture_output=True, check=True).stdout
    return [line for line in out.splitlines() if line]


def reference_corpus(files: list[str]) -> list[tuple[str, str]]:
    """Return (path, text) for every maintained file a reference may live in."""
    corpus = []
    for rel in files:
        if rel == "audits/check_repo_minimal.py":
            continue  # this script names every audited tree; not a reference
        path = ROOT / rel
        if Path(rel).suffix not in REFERENCE_SOURCES or not path.is_file():
            continue
        try:
            corpus.append((rel, path.read_text(encoding="utf-8", errors="replace")))
        except OSError:
            continue
    return corpus


def is_referenced(rel: str, corpus: list[tuple[str, str]]) -> str | None:
    basename = Path(rel).name
    # Path references win over basenames so a fixture shared by name wins only
    # when the full path is never spelled out anywhere.
    base_pattern = re.compile(r"(?<![\w./-])" + re.escape(basename) + r"(?![\w-]|\.\w)")
    for source, text in corpus:
        if source == rel:
            continue
        if rel in text:
            return source
    for source, text in corpus:
        if source == rel:
            continue
        if base_pattern.search(text):
            return source
    return None


def stale_allow_entries(files: list[str]) -> list[str]:
    return [rel for rel in ALLOW_LIST if rel not in files]


def main(argv: list[str]) -> int:
    files = tracked_files()
    errors: list[str] = []

    for rel in files:
        if rel.startswith(EXCLUDED_ROOTS) or rel.endswith(".log"):
            errors.append(f"{rel}: coordination artifact or log must not be tracked")
        if Path(rel).name in FORBIDDEN_TRACKED_NAMES:
            errors.append(f"{rel}: plan/brief documents are not repository content")

    corpus = reference_corpus(files)
    audited: list[str] = []
    for rel in files:
        if not rel.startswith(tuple(t + "/" for t in ("audits", "Tests", "specification"))):
            continue
        if rel.startswith(EXCLUDED_PREFIXES):
            continue
        audited.append(rel)

    if "--tracked-only" in argv and not audited:
        print("repo-minimal: no tracked support files (nothing to audit)")
        return 0

    orphans = [rel for rel in audited
               if rel not in ALLOW_LIST and is_referenced(rel, corpus) is None]
    for rel in orphans:
        errors.append(f"{rel}: not referenced by any script, target, import, "
                      "test or maintained document (add a use or an allow-list "
                      "entry with a justification)")

    for rel in stale_allow_entries(files):
        if is_referenced(rel, corpus) is not None:
            errors.append(f"{rel}: allow-list entry is stale (the file is "
                          "referenced now); remove it from ALLOW_LIST")

    if errors:
        for err in errors:
            print(f"ERROR: {err}", file=sys.stderr)
        print(f"repo-minimal: FAIL ({len(errors)} error(s); "
              f"{len(audited)} support files audited, "
              f"{len(audited) - len([o for o in orphans])} referenced)",
              file=sys.stderr)
        return 1

    print(f"repo-minimal: PASS ({len(audited)} support files audited, "
          f"{len(ALLOW_LIST)} allow-listed, no coordination artifacts tracked)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
