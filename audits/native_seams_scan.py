#!/usr/bin/env python3
"""Parser for the source-level native substitutions (`@[csimp]`, `@[implemented_by]`).

Lean's compiler-`csimp` state is *not* imported from `.olean` files
(`addImportedFn := fun _ _ => pure []` in `Lean/Compiler/CSimpAttr.lean`), and
the `@[implemented_by]` pairs the environment does expose are mixed with the
elaborator-generated `ctorIdx` ones.  This module re-derives both seams from the
tree with a parser instead of a `grep`:

* comments (`--`, nested `/- -/`) are blanked before matching, so a mention
  inside a comment or a docstring never counts;
* both attribute spellings are handled — `@[csimp] theorem f : @g = @h` and
  `attribute [csimp] …,` same for `implemented_by`, with the target on the same
  line or on the next non-blank line;
* names are fully qualified through the surrounding `namespace` stack.

It is used by `audits/check_native_seams.sh` to compare the tree against
`audits/native_seams.json` and to hand the `csimp` list to `NativeSeams.lean`:

    python3 audits/native_seams_scan.py            # all seams, TSV
    python3 audits/native_seams_scan.py csimp      # only @[csimp]
    python3 audits/native_seams_scan.py impl_by    # only @[implemented_by]
"""

from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SCAN_ROOT = ROOT / "LeanFzn"

NAME = r"[\w.'?\u2080-\u209c]+"
BIND = r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+)*"
THEOREM_RE = re.compile(rf"^{BIND}theorem\s+({NAME})\s*:")
DEF_RE = re.compile(rf"^{BIND}def\s+([\w'?]+)")
CSIMP_INLINE_RE = re.compile(
    rf"^@\[csimp\]\s*{BIND}theorem\s+({NAME})\s*:\s*@?({NAME})\s*=\s*@?({NAME})")
IMPL_BY_INLINE_RE = re.compile(
    rf"^@\[implemented_by\s+({NAME})\]\s*{BIND}def\s+([\w'?]+)")
ATTR_IMPL_BY_RE = re.compile(rf"^attribute\s+\[implemented_by\s+({NAME})\]")
ATTR_CSIMP_RE = re.compile(r"^attribute\s+\[csimp\]\s*$")
ATTR_CSIMP_INLINE_RE = re.compile(
    rf"^attribute\s+\[csimp\]\s+{BIND}theorem\s+([\w']+)\s*:\s*@?({NAME})\s*=\s*@?({NAME})")
EQ_RE = re.compile(rf"^@?({NAME})\s*=\s*@?({NAME})")


def strip_comments(src: str) -> str:
    """Blank out `--` and nested `/- -/` comments, preserving line structure."""
    out: list[str] = []
    i, n, depth = 0, len(src), 0
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
        out.append(src[i])
        i += 1
    return "".join(out)


@dataclass
class Seam:
    kind: str          # "impl_by" | "csimp"
    ref: str           # fully qualified reference declaration
    impl: str          # fully qualified implementation declaration
    thm: str | None    # for `csimp`, the source theorem name
    file: str


def fq(stack: list[str], leaf: str) -> str:
    """Fully qualify `leaf` through the namespace stack.

    A dotted name is qualified component by component: `DomC.hi?` inside
    `namespace LeanFzn.Engine` is `LeanFzn.Engine.DomC.hi?`, and a name that is
    already absolute (`LeanFzn…`) is left alone.  This is the same rule the
    kernel uses for declaration names.
    """
    if leaf.startswith("LeanFzn"):
        return leaf
    if "." in leaf:
        head = leaf.split(".", 1)[0]
        for i in range(len(stack), 0, -1):
            candidate = ".".join(stack[:i] + [leaf])
            # A dotted name is qualified by the innermost namespace whose last
            # component matches the name's head (`DomC`), otherwise by the
            # whole stack.
            if stack[i - 1].split(".")[-1] == head:
                return candidate
        return ".".join(stack + [leaf]) if stack else leaf
    return ".".join(stack + [leaf]) if stack else leaf


def next_nonblank(lines: list[str], start: int) -> str:
    for line in lines[start:]:
        if line.strip():
            return line.strip()
    return ""


def seams_in(path: Path) -> list[Seam]:
    src = strip_comments(path.read_text(encoding="utf-8"))
    lines = src.split("\n")
    rel = str(path.relative_to(ROOT))
    stack: list[str] = []
    seams: list[Seam] = []
    pending_impl_by: str | None = None    # attribute target, waiting for `def`
    pending_csimp_thm: str | None = None  # `@[csimp] theorem f :` waiting for `=`
    pending_ns: list[str] = []             # namespace stack at that theorem
    for idx, raw in enumerate(lines):
        line = raw.strip()
        m = re.match(r"^namespace\s+([\w.]+)", line)
        if m:
            stack.append(m.group(1))
            continue
        m = re.match(r"^end\s+([\w.]+)\s*$", line)
        if m:
            # `end <name>` closes a `section`/`namespace`; only pop when the
            # name actually matches the innermost one, so `end SpecEq` does not
            # close `namespace LeanFzn.Compiler`.
            if stack and (stack[-1] == m.group(1) or
                          stack[-1].split(".")[-1] == m.group(1).split(".")[-1]):
                stack.pop()
            continue

        # 1. `@[implemented_by impl] def ref …` (def possibly on a later line).
        if pending_impl_by is not None:
            d = DEF_RE.match(line)

            if d:
                seams.append(Seam("impl_by", fq(stack, d.group(1)),
                                  pending_impl_by, None, rel))
                pending_impl_by = None
                continue
            if line.startswith("attribute") or (line.startswith("/-")):
                # Another attribute or doc comment in between: the pending
                # `@[implemented_by]` still binds the next `def`.
                continue
            if line and not line.startswith("@["):
                pending_impl_by = None
        m = IMPL_BY_INLINE_RE.match(line)
        if m:
            seams.append(Seam("impl_by", fq(stack, m.group(2)),
                              fq(stack, m.group(1)), None, rel))
            continue
        m = re.match(rf"^@\[implemented_by\s+({NAME})\]\s*$", line)
        if m:
            pending_impl_by = fq(stack, m.group(1))
            continue

        # 2. `attribute [implemented_by impl] ref`
        m = ATTR_IMPL_BY_RE.match(line)
        if m:
            impl = fq(stack, m.group(1))
            rest = line[m.end():].strip()
            if rest:
                seams.append(Seam("impl_by", fq(stack, rest.split()[0]), impl,
                                  None, rel))
            else:
                # `attribute [implemented_by f]` on its own line: the target
                # declaration precedes the attribute (Lean's `attribute` syntax
                # names the target *before* the bracket list in the second
                # form; in this form there is none, so it applies to the most
                # recent matching declaration).
                nxt = next_nonblank(lines, idx + 1)
                if nxt and not nxt.startswith("attribute"):
                    seams.append(Seam("impl_by", fq(stack, nxt.split()[0]), impl,
                                      None, rel))
            continue

        # 3. `@[csimp] theorem f : @g = @h` on one line.
        m = CSIMP_INLINE_RE.match(line)
        if m:
            seams.append(Seam("csimp", fq(stack, m.group(2)),
                              fq(stack, m.group(3)), fq(stack, m.group(1)), rel))
            continue
        if pending_csimp_thm is not None:
            m = EQ_RE.match(line)
            if m:
                seams.append(Seam("csimp", fq(pending_ns, m.group(1)),
                                  fq(pending_ns, m.group(2)), pending_csimp_thm,
                                  rel))
            pending_csimp_thm = None
            continue
        m = re.match(rf"^@\[csimp\]\s*{BIND}theorem\s+({NAME})\s*:\s*$", line)
        if m:
            pending_csimp_thm = fq(stack, m.group(1))
            pending_ns = list(stack)
            continue
        m = ATTR_CSIMP_INLINE_RE.match(line)
        if m:
            seams.append(Seam("csimp", fq(stack, m.group(2)),
                              fq(stack, m.group(3)), fq(stack, m.group(1)), rel))
            continue
        if ATTR_CSIMP_RE.match(line):
            nxt = next_nonblank(lines, idx + 1)
            m = THEOREM_RE.match(nxt)
            if m:
                pending_csimp_thm = fq(stack, m.group(1))
            continue
    return seams


ALIASES = ROOT / "audits" / "native_seams_aliases.json"


def load_aliases() -> dict[str, dict[str, str]]:
    import json
    if not ALIASES.is_file():
        return {}
    data = json.loads(ALIASES.read_text(encoding="utf-8"))
    return {k: data.get(k, {}) for k in ("ref", "thm")}


def all_seams() -> list[Seam]:
    aliases = load_aliases()
    ref_fix = aliases.get("ref", {})
    thm_fix = aliases.get("thm", {})
    out: list[Seam] = []
    for path in sorted(SCAN_ROOT.rglob("*.lean")):
        for s in seams_in(path):
            if s.ref in ref_fix:
                s = Seam(s.kind, ref_fix[s.ref], s.impl, s.thm, s.file)
            if s.ref in thm_fix:
                s = Seam(s.kind, s.ref, s.impl, thm_fix[s.ref], s.file)
            out.append(s)
    return out


def main() -> int:
    kind = sys.argv[1] if len(sys.argv) > 1 else "all"
    seams = all_seams()
    if kind != "all":
        seams = [s for s in seams if s.kind == kind]
    for s in seams:
        print(f"{s.kind}\t{s.ref}\t{s.impl}\t{s.thm or '-'}\t{s.file}")
    print(f"# {len(seams)} seams", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
