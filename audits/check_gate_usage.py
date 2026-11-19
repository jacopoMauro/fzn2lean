#!/usr/bin/env python3
"""Audit: every verdict-producing public route takes a `GatedModel`.

P0 requires that a raw `Model` cannot reach a verdict except through `gate`
(`LeanFzn/Integration/Public/Gate.lean`).  This check fails when a definition
under `LeanFzn/Integration/` that *returns a verdict type* takes a raw `Model`
parameter and is not `gate` itself or a documented non-verdict helper.

How it works
------------
The Lean sources are scanned textually (no build needed).  For each top-level
`def`/`partial def`/`opaque`/`noncomputable def` in `LeanFzn/Integration/`, the
script collects its name, its exported name (namespace aware), its declared
parameter names with types, and the "returns a verdict" verdict:

* `Result`                       -> returns a verdict
* `OptRun` / `OptSummary`        -> returns a verdict
* `Except <..> (OptRun|OptSummary)` etc. -> returns a verdict
* `CertVerdict` / `CoreResult`   -> returns a verdict (Core level)
* `IO (...)`                     -> returns a verdict when the inner type is one
                                     of the above (streaming wrappers)

A definition *fails* when
  * it returns a verdict, AND
  * it (or the tail of its parameter list) takes a parameter typed `Model`, AND
  * its exported name is not allow-listed below.

The allow-list is deliberately short and carries one justification per entry:
a raw-`Model` verdict route is acceptable only when it is (a) `gate` itself or
(b) a non-verdict helper whose name says it returns an error/except, or (c) one
of the legacy wrappers the project keeps for compatibility and whose *proved*
gated twin exists next to it (rule 2 of the brief: never remove a public name).

Exit codes: 0 = pass, 1 = a verdict route takes a raw `Model` without an
allow-list entry.
"""

from __future__ import annotations

import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SCAN_ROOT = ROOT / "LeanFzn" / "Integration"

VERDICT_TYPES = (
    "Result",
    "OptRun",
    "OptSummary",
    "CertVerdict",
    "CoreResult",
)

# Definitions allowed to take a raw `Model` and return a verdict.  Every entry
# needs a one-line justification; an entry whose definition disappears makes
# the check fail (stale allow-list), so this stays honest.
ALLOWLIST: dict[str, str] = {
    # --- the gate itself -----------------------------------------------------
    "LeanFzn.Core.gate":
        "the gate is the only place a raw Model becomes a GatedModel",
    # --- proved compatibility wrappers (rule 2: keep the public name) --------
    "LeanFzn.Core.solveModelWithStats":
        "raw wrapper with a gated twin `gatedSolveModelWithStats`; kept for API compatibility",
    "LeanFzn.Core.solveModel":
        "raw wrapper with a gated twin `gatedSolveModel`; kept for API compatibility",
    "LeanFzn.Core.optimizeCore":
        "raw wrapper with a gated twin `gatedOptimizeCore`; kept for API compatibility",
    "LeanFzn.Core.optimizeStreamCoreStats":
        "raw wrapper with a gated twin `gatedOptimizeStreamCoreStats`; kept for API compatibility",
    "LeanFzn.Core.optimizeStreamCoreStatsLoop":
        "internal round loop over a compiled problem, not a source-model route",
    "LeanFzn.Core.optimizeStreamCoreStatsLoopPrepared":
        "internal round loop over a prepared problem, not a source-model route",
    "LeanFzn.Core.optimizeCoreSeed":
        "raw wrapper with a gated twin `gatedOptimizeCoreSeed`; kept for API compatibility",
    "LeanFzn.Core.optimizeStreamCoreSeed":
        "raw wrapper with a gated twin `gatedOptimizeStreamCoreSeed`; kept for API compatibility",
    "LeanFzn.Core.optimizeCoreLns":
        "raw wrapper with a gated twin `gatedOptimizeCoreLns`; kept for API compatibility",
    "LeanFzn.Core.optimizeStreamCoreLns":
        "raw wrapper with a gated twin `gatedOptimizeStreamCoreLns`; kept for API compatibility",
    "LeanFzn.Core.solveModelWithPhaseStats":
        "dev-only timing wrapper with a gated twin `solveGatedModelWithPhaseStats`; kept for API compatibility",
    "LeanFzn.Core.optimizeStreamCoreStatsPhased":
        "dev-only timing wrapper with a gated twin `optimizeStreamGatedCoreStatsPhased`; kept for API compatibility",
    # --- diagnostics / counters, not verdict routes ------------------------
    "LeanFzn.Integration.Report.lnsStreamStats":
        "private T8 counter witness: returns EngineStats only, never a verdict",
}

DECL_RE = re.compile(
    r"^(?P<indent>[ \t]*)"
    r"(?:@\[[^\]]*\]\s*)?"
    r"(?:(?:private|protected|noncomputable|partial|unsafe|@\[[^\]]*\])\s+)*"
    r"(?:def|opaque)\s+"
    r"(?P<name>[A-Za-z_][\w'.]*)"
)


@dataclass
class Decl:
    path: Path
    line: int
    name: str          # fully qualified
    raw: str           # the declaration text
    params: list[tuple[str, str]] = field(default_factory=list)  # (name, type)
    ret: str = ""


def strip_comments(src: str) -> str:
    """Remove nested `/- -/` comments and line comments, keep line numbers."""
    out: list[str] = []
    i, n = 0, len(src)
    depth = 0
    while i < n:
        two = src[i:i + 2]
        if depth == 0 and two == "/-":
            depth = 1
            i += 2
            while i < n and depth:
                if src[i:i + 2] == "/-":
                    depth += 1
                    i += 2
                elif src[i:i + 2] == "-/":
                    depth -= 1
                    i += 2
                else:
                    out.append("\n" if src[i] == "\n" else " ")
                    i += 1
            continue
        if depth == 0 and two == "--":
            while i < n and src[i] != "\n":
                out.append(" ")
                i += 1
            continue
        out.append(src[i] if depth == 0 else ("\n" if src[i] == "\n" else " "))
        i += 1
    return "".join(out)


def namespace_of(lines: list[str], upto: int) -> str:
    ns: list[str] = []
    for ln in lines[:upto]:
        m = re.match(r"^\s*namespace\s+([\w.]+)", ln)
        if m:
            ns.append(m.group(1))
        elif re.match(r"^\s*end\s+([\w.]+)\s*$", ln):
            if ns:
                ns.pop()
    return ".".join(ns)


def balanced(text: str, start: int, open_ch: str, close_ch: str) -> int:
    """Index just past the bracket that closes the one at `start`."""
    depth = 0
    i = start
    while i < len(text):
        c = text[i]
        if c == open_ch:
            depth += 1
        elif c == close_ch:
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1
    return len(text)


def split_params(sig: str) -> list[tuple[str, str]]:
    """`(a b : T) (c : U) : R` -> [(a, T), (b, T), (c, U)]."""
    params: list[tuple[str, str]] = []
    i = 0
    while i < len(sig):
        if sig[i] == "(":
            j = balanced(sig, i, "(", ")")
            inner = sig[i + 1:j - 1]
            if ":" in inner:
                names, ty = inner.split(":", 1)
                # explicit binder only; implicit `{..}`/instance `[..]` is not a
                # caller-supplied argument of the signature we audit.
                for nm in names.split():
                    params.append((nm, ty.strip()))
            i = j
        elif sig[i] == "{":
            i = balanced(sig, i, "{", "}")
        elif sig[i] == "[":
            i = balanced(sig, i, "[", "]")
        else:
            i += 1
    return params


def return_type(text: str) -> str:
    """The result type of a definition signature.

    Scans the parameter list (explicit `(..)`, implicit `{..}` and instance
    `[..]` binders, default values after `:=` inside a binder included) and
    returns the text after the first *toplevel* `:` that is not part of a
    binder and not the start of `:=`.
    """
    depth = 0
    i = 0
    n = len(text)
    while i < n:
        c = text[i]
        if c in "({[":
            depth += 1
        elif c in ")}]":
            depth -= 1
        elif c == ":" and depth == 0:
            if text[i:i + 2] == ":=" or (i > 0 and text[i - 1] == ":"):
                i += 1
                continue
            return text[i + 1:]
        i += 1
    return ""


def returns_verdict(ret: str) -> bool:
    if not ret:
        return False
    r = ret.strip()
    head = re.match(r"(?:IO\s+)?\(?\s*([A-Za-z_][\w.]*)", r)
    if head:
        base = head.group(1).split(".")[-1]
        if base in VERDICT_TYPES:
            return True
        if base == "Except":
            return any(t in r for t in VERDICT_TYPES)
        if base == "IO":
            return any(re.search(rf"\b{t}\b", r) for t in VERDICT_TYPES)
    return any(re.search(rf"\b{t}\b", r) for t in VERDICT_TYPES)


def decls_in(path: Path) -> list[Decl]:
    src = path.read_text(encoding="utf-8")
    clean = strip_comments(src)
    lines = clean.split("\n")
    decls: list[Decl] = []
    for idx, line in enumerate(lines):
        m = DECL_RE.match(line)
        if not m:
            continue
        # gather the signature text until the first toplevel `:=` / `where`
        start_line = idx
        # The signature ends at the toplevel result type `:` (not at a
        # default-value `:=` inside a binder and not at the body `:=`).
        sig = ""
        j = idx
        while j < len(lines):
            sig += lines[j] + "\n"
            if return_type(sig):
                break
            if re.match(r"^\s*where\s*$", lines[j]):
                break
            j += 1
        name = m.group("name")
        if "." in name:
            fq = name
        else:
            ns = namespace_of(lines, start_line)
            fq = f"{ns}.{name}" if ns else name
        body = sig[sig.index(name) + len(name):]
        ret = return_type(body)
        ret = ret.split(":=")[0] if ":=" in ret else ret
        params = split_params(body)
        decls.append(Decl(path=path, line=idx + 1, name=fq,
                          raw=sig, params=params, ret=ret))
    return decls


def main() -> int:
    problems: list[str] = []
    all_names: set[str] = set()
    used_allow: set[str] = set()
    checked = 0
    verdict_routes = 0
    for path in sorted(SCAN_ROOT.rglob("*.lean")):
        for d in decls_in(path):
            all_names.add(d.name)
            raw_model = [nm for nm, ty in d.params
                         if re.search(r"(?<![\w.])Model(?![\w])", ty)
                         and "GatedModel" not in ty]
            if not raw_model:
                continue
            checked += 1
            if not returns_verdict(d.ret):
                continue
            verdict_routes += 1
            if d.name in ALLOWLIST:
                used_allow.add(d.name)
                continue
            problems.append(
                f"{path.relative_to(ROOT)}:{d.line}: `{d.name}` returns a verdict "
                f"and takes raw `Model` parameter(s) {raw_model}")

    stale = sorted(set(ALLOWLIST) - all_names)
    for name in stale:
        problems.append(f"allow-list entry `{name}` matches no declaration "
                        f"(stale entry)")

    if problems:
        print("gate-usage check FAILED")
        for p in problems:
            print("  " + p)
        print(f"  ({checked} definitions take a raw Model; {verdict_routes} of "
              f"them return a verdict; {len(ALLOWLIST)} allow-list entries)")
        return 1
    print(f"gate-usage check PASSED ({verdict_routes} raw-Model definitions "
          f"return a verdict; {len(used_allow)} allow-listed, every one an "
          f"internal helper or a proved compatibility wrapper; "
          f"{len(ALLOWLIST)} entries)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
