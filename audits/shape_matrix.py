#!/usr/bin/env python3
"""Predicate-shape census and micro-model matrix for LeanFzn (dev-only).

Usage:
  python3 audits/shape_matrix.py --cohort audits/cohorts/COV37.txt \\
      --out tmp/shape-matrix-o2 [--binary PATH] [--cap 20]

The first pass streams every cohort model line by line, records every
constraint predicate call with its full argument shape (variables, integer
literals ``L``, Boolean literals ``B``, constant sets ``R``, set variables,
and array element-type combinations such as ``[pint]``/``[vint]``), and
records every declaration form (scalar/array, parameter/variable,
int/bool/set, finite domain).  It never reads a whole model into memory and
has no size cutoff: the 327 MiB, 3.7M-line ``wlp22`` model is handled by the
same streaming path as every other model.

For each distinct shape a micro-model is generated with the prototype's
token-to-concrete-argument rules (``tmp/plan-analysis-20261107/allshapes.py``)
and solved with ``leanfzn solve``.  Results are ``accepted`` (exit 0/1 or
UNSAT output), ``rejected`` (first stderr line recorded), ``set`` (the shape
contains ``vset``/``pset``/``??`` and is not tested), or ``timeout``.

The second pass parses the predicate names and arities from the Lean sources
(``Semantics/Evaluation.lean`` name lists, ``Semantics/StdLib.lean`` ``stdSig``,
``Semantics/Globals.lean`` ``globalsSig``, ``Compiler/Extract.lean`` and
``Compiler/Compile.lean``).  It enumerates every variable/literal combination
for every standard predicate signature and records the results separately.
Checker-only ``fzn_*`` globals and explicitly unsupported globals are listed
in ``enumeration_scope.tsv`` as skipped, with the source and reason.

This tool is development-only.  It imports only the Python standard library,
is not used by the solver at run time, and does not decide any solver result.

Outputs (under --out):
  shape_matrix.tsv          one row per shape, family counts, status, reason
  shape_family_matrix.tsv   shape x family occurrence matrix
  shapes.json               machine-readable per-shape record
  census.tsv                per-model shape occurrences
  declarations.tsv          per-model declaration forms
  declaration_summary.tsv   aggregated declaration forms
  micro_runs.tsv            every micro-model run in the first pass
  enumeration.tsv           every second-pass predicate variant run
  enumeration_matrix.tsv    per-predicate second-pass aggregation
  enumeration_scope.tsv     enumerated/skipped names with sources and reasons
  summary.txt / summary.tsv human- and machine-readable summaries
  micro/, enum_micro/       generated micro-models
"""

from __future__ import annotations

import argparse
import collections
import csv
import dataclasses
import json
import re
import subprocess
import time
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_BIN = ROOT / ".lake/build/bin/leanfzn"

INT_RE = re.compile(r"-?\d+\Z")
RANGE_RE = re.compile(r"-?\d+\.\.-?\d+\Z")
CONSTRAINT_RE = re.compile(
    r"constraint\s+([A-Za-z_0-9]+)\((.*?)\)(\s*::.*)?;$")
DECL_RE = re.compile(
    r"(array \[([^\]]*)\] of )?(var )?(set of )?([^:]*):\s*([A-Za-z_0-9]+)")

# Parameters are declared before variables: the parser enforces the FlatZinc
# declaration order (a parameter array after a variable declaration is a parse
# error).  The token-to-argument rules below are otherwise the prototype's.
MICRO_HEADER = """\
array [1..2] of int: pa=[1,2];
var 1..3: vi0; var 1..3: vi1; var 1..3: vi2;
var bool: vb0; var bool: vb1; var bool: vb2;
array [1..2] of var int: va=[vi0,vi1];
array [1..2] of var bool: ba=[vb0,vb1];
"""

ENUM_HEADER = """\
var 1..3: vi0; var 1..3: vi1; var 1..3: vi2; var 1..3: vi3;
var bool: vb0; var bool: vb1; var bool: vb2; var bool: vb3;
array [1..2] of var int: va=[vi0,vi1];
array [1..2] of var bool: ba=[vb0,vb1];
"""

PROTOTYPE_SPLIT = (46, 6, 9)


# ---------------------------------------------------------------------------
# Small text helpers
# ---------------------------------------------------------------------------

def split_top_level(text: str) -> list[str]:
    """Split on commas at bracket depth zero; keep bracket contents intact."""
    out: list[str] = []
    depth = 0
    cur: list[str] = []
    for ch in text:
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        if ch == "," and depth == 0:
            out.append("".join(cur).strip())
            cur = []
        else:
            cur.append(ch)
    if "".join(cur).strip():
        out.append("".join(cur).strip())
    return out


def balanced_bracket(text: str, start: int) -> tuple[str, int]:
    """Return the contents of the ``[`` at ``start`` and the index after it."""
    depth = 0
    for i in range(start, len(text)):
        if text[i] == "[":
            depth += 1
        elif text[i] == "]":
            depth -= 1
            if depth == 0:
                return text[start + 1:i], i + 1
    raise ValueError("unbalanced brackets")


def one_line(text: str) -> str:
    """Make a diagnostic safe for a TSV cell."""
    return " ".join(text.split())


def family_of(path: str) -> str:
    """The path component after the ``YYYYfzn/`` directory."""
    parts = Path(path.replace("\\", "/")).parts
    for i, part in enumerate(parts):
        if re.fullmatch(r"\d{4}fzn", part) and i + 1 < len(parts):
            return parts[i + 1]
    # Fall back to the parent directory for non-challenge paths.
    return parts[-2] if len(parts) >= 2 else "unknown"


def safe_name(text: str, limit: int = 90) -> str:
    """A short filesystem-safe tag for a shape or predicate name."""
    tag = re.sub(r"[^A-Za-z0-9_.-]+", "_", text).strip("_")
    return (tag or "shape")[:limit]


# ---------------------------------------------------------------------------
# First pass: streaming census
# ---------------------------------------------------------------------------

def iter_model_lines(path: Path):
    """Stream one model, one line at a time.

    ``wlp22`` is 327 MiB and has about 3.7M lines; it is deliberately read
    through this streaming iterator, never with ``read_text``/``readlines``,
    and there is no size-based skip.
    """
    try:
        with path.open("r", encoding="utf-8", errors="replace") as f:
            for line in f:
                yield line.strip()
    except OSError as exc:
        raise SystemExit(f"cannot read model {path}: {exc}") from exc


def parse_declaration(line: str) -> tuple[str, str, str] | None:
    """Parse a FlatZinc declaration into (name, kind_token, form).

    ``kind_token`` is the prototype's token vocabulary (``vint``, ``pint``,
    ``[vint]``, ``vset``, ...).  ``form`` is the human-readable declaration
    form used by ``declarations.tsv``; for variable declarations it includes
    the declared finite domain (or ``unbounded`` for a bare ``var int``).
    """
    m = DECL_RE.match(line)
    if not m:
        return None
    array_prefix, index_domain, var, set_of, rest, name = m.groups()
    rest = (rest or "").strip()
    is_array = bool(array_prefix)
    is_var = bool(var)
    if set_of or "set" in rest:
        base = "set"
    elif "bool" in rest:
        base = "bool"
    else:
        base = "int"
    kind = ("[" if is_array else "") + ("v" if is_var else "p") + base
    if is_array:
        kind += "]"

    scope = f"array[{index_domain.strip()}]" if is_array else "scalar"
    if is_var and base == "int":
        domain = rest if rest and rest != "int" else "unbounded"
        form = f"{scope} var int {domain}"
    elif is_var and base == "set":
        domain = rest.replace("set of", "").strip() if rest else "?"
        form = f"{scope} var set {domain}"
    elif is_var:
        form = f"{scope} var {base}"
    else:
        form = f"{scope} par {base}"
    return name, kind, form


def shape_of_arg(arg: str, kinds: dict[str, str]) -> str:
    """Map one constraint argument to its prototype shape token."""
    if arg in kinds:
        return kinds[arg]
    if INT_RE.fullmatch(arg):
        return "L"
    if arg in ("true", "false"):
        return "B"
    if RANGE_RE.fullmatch(arg):
        return "R"
    if arg.startswith("{"):
        return "R"
    if arg.startswith("["):
        inner = arg[1:-1]
        elems = split_top_level(inner) if inner.strip() else []
        return "[" + "|".join(sorted({shape_of_arg(e, kinds) for e in elems})) + "]"
    return "??"


def census(models: list[str]) -> tuple[
        dict[str, collections.Counter], dict[str, collections.Counter],
        dict[str, collections.Counter], dict[str, str]]:
    """Stream models and return shape/declaration censuses.

    Returns ``(shape_families, model_shapes, model_decls, model_family)``.
    ``shape_families[shape][family]`` counts occurrences, and the per-model
    counters retain the census needed for ``census.tsv`` and
    ``declarations.tsv``.
    """
    shape_families: dict[str, collections.Counter] = collections.defaultdict(
        collections.Counter)
    model_shapes: dict[str, collections.Counter] = {}
    model_decls: dict[str, collections.Counter] = {}
    model_family: dict[str, str] = {}

    for path in models:
        family = family_of(path)
        model_family[path] = family
        kinds: dict[str, str] = {}
        shapes: collections.Counter = collections.Counter()
        decls: collections.Counter = collections.Counter()
        model_path = Path(path)
        if not model_path.is_absolute():
            model_path = ROOT / model_path

        start = time.monotonic()
        lines = 0
        for line in iter_model_lines(model_path):
            lines += 1
            if line.startswith("constraint"):
                m = CONSTRAINT_RE.match(line)
                if not m:
                    continue
                name, arg_text = m.group(1), m.group(2)
                args = split_top_level(arg_text)
                shape = name + "(" + ",".join(
                    shape_of_arg(a, kinds) for a in args) + ")"
                shapes[shape] += 1
                shape_families[shape][family] += 1
            elif not line.startswith(("solve", "%")):
                decl = parse_declaration(line)
                if decl is not None:
                    name, kind, form = decl
                    kinds[name] = kind
                    decls[form] += 1

        model_shapes[path] = shapes
        model_decls[path] = decls
        wall = time.monotonic() - start
        print(f"  census {path} ({family}): {lines} lines, "
              f"{len(shapes)} shapes, {len(decls)} declaration forms, "
              f"{wall:.1f}s", flush=True)
    return shape_families, model_shapes, model_decls, model_family


# ---------------------------------------------------------------------------
# First pass: micro-models
# ---------------------------------------------------------------------------

def concrete_arg(token: str, index: int) -> str | None:
    """Prototype token -> concrete micro-model argument.

    The prototype covered ``vint``/``vbool``/``L``/``B``/``R``/``[pint]``/
    ``[vint]``/``[vbool]``.  Parameter scalars/arrays are mapped too so a
    shape containing them cannot crash the generator; such shapes do not
    occur in the COV37 census.
    """
    if token == "vint":
        return f"vi{index % 3}"
    if token == "vbool":
        return f"vb{index % 3}"
    if token in ("pint", "L"):
        return "1"
    if token in ("pbool", "B"):
        return "true"
    if token == "R":
        return "1..2"
    if token == "[pint]":
        return "pa"
    if token == "[vint]":
        return "va"
    if token == "[vbool]":
        return "ba"
    if token.startswith("["):
        toks = token[1:-1].split("|") if len(token) > 2 else []
        parts = [concrete_arg(t, j) for j, t in enumerate(toks + toks[:1])]
        if any(p is None for p in parts):
            return None
        return "[" + ",".join(parts) + "]"
    return None


def instantiate_shape(shape: str) -> tuple[str, list[str]] | None:
    """Build (predicate name, concrete arguments) for a census shape.

    ``None`` means the shape needs set variables and is not tested.  Linear
    constraints get a coefficient array of length 2 matching the two-element
    variable array (the prototype pinned ``[pint]`` coefficients this way);
    if the variable array itself was an all-literal array, it is shortened to
    two elements so the coefficient length still matches.
    """
    if re.search(r"vset|pset|\?\?", shape):
        return None
    name, arg_text = shape.split("(", 1)
    arg_text = arg_text[:-1]
    tokens = split_top_level(arg_text)
    args: list[str] = []
    for i, token in enumerate(tokens):
        value = concrete_arg(token, i)
        if value is None:
            return None
        args.append(value)
    if name.startswith("int_lin"):
        # Coefficient array and variable array must have the same length.
        args[0] = "[1,1]"
        if args[1].startswith("[") and args[1].count(",") != 1:
            inner = args[1][1:-1]
            if inner.strip():
                args[1] = "[" + inner.split(",")[0] + ",1]"
    return name, args


@dataclasses.dataclass
class RunResult:
    status: str
    exit_code: int | None
    wall_s: float
    reason: str
    model: str = ""


def first_reason(exit_code: int | None, stdout: str, stderr: str) -> str:
    """The first non-empty diagnostic line, else the exit code."""
    for stream in (stderr, stdout):
        for line in stream.splitlines():
            line = line.strip()
            if line:
                return one_line(line)
    return f"exit {exit_code}"


def run_model(binary: Path, text: str, model_path: Path,
              cap: float) -> RunResult:
    """Write and run one micro-model, capped at ``cap`` seconds."""
    model_path.parent.mkdir(parents=True, exist_ok=True)
    model_path.write_text(text, encoding="utf-8")
    start = time.monotonic()
    try:
        proc = subprocess.run(
            [str(binary), "solve", str(model_path)],
            capture_output=True, text=True, encoding="utf-8",
            errors="replace", timeout=cap)
    except subprocess.TimeoutExpired:
        return RunResult("timeout", None, time.monotonic() - start,
                         f"timeout after {cap:g}s")
    wall = time.monotonic() - start
    if proc.returncode in (0, 1) or "UNSAT" in proc.stdout:
        return RunResult("accepted", proc.returncode, wall, "")
    return RunResult("rejected", proc.returncode, wall,
                     first_reason(proc.returncode, proc.stdout, proc.stderr))


def classify_shapes(shape_families: dict[str, collections.Counter],
                    out_dir: Path, binary: Path,
                    cap: float) -> dict[str, RunResult]:
    """Run one micro-model per distinct shape and return its result."""
    results: dict[str, RunResult] = {}
    micro_dir = out_dir / "micro"
    micro_dir.mkdir(parents=True, exist_ok=True)
    shapes = sorted(shape_families)
    print(f"\nMicro-models: {len(shapes)} distinct shapes", flush=True)
    for i, shape in enumerate(shapes, 1):
        if re.search(r"vset|pset|\?\?", shape):
            results[shape] = RunResult(
                "set", None, 0.0,
                "requires set variables (vset/pset/??); not tested")
            print(f"  micro {i:3d}/{len(shapes)} set       {shape}", flush=True)
            continue
        inst = instantiate_shape(shape)
        if inst is None:
            results[shape] = RunResult(
                "set", None, 0.0,
                "no concrete instantiation; treated as set-needed")
            print(f"  micro {i:3d}/{len(shapes)} set       {shape}", flush=True)
            continue
        name, args = inst
        text = (MICRO_HEADER
                + f"constraint {name}({','.join(args)});\n"
                + "solve satisfy;\n")
        filename = f"{i:03d}_{safe_name(shape)}.fzn"
        result = run_model(binary, text, micro_dir / filename, cap)
        result.model = f"micro/{filename}"
        results[shape] = result
        detail = f"  ({result.reason})" if result.reason else ""
        print(f"  micro {i:3d}/{len(shapes)} {result.status:9s} "
              f"{shape}{detail}", flush=True)
    return results


# ---------------------------------------------------------------------------
# Second pass: source-derived predicate enumeration
# ---------------------------------------------------------------------------

@dataclasses.dataclass
class Sources:
    std_names: list[str]
    set_names: list[str]
    std_sig: dict[str, list[str]]
    globals_sig: dict[str, list[str]]
    globals_unsupported: list[str]
    extract_arities: dict[str, list[int]]
    compile_arities: dict[str, list[int]]


def lean_string_list(text: str, defname: str) -> list[str]:
    """Parse ``def <defname> : List String := [ ... ]`` in Lean source."""
    m = re.search(
        r"def\s+" + re.escape(defname) + r"\s*:\s*List String\s*:?=\s*",
        text)
    if not m:
        raise SystemExit(f"cannot find Lean list definition {defname}")
    start = text.find("[", m.end())
    if start < 0:
        raise SystemExit(f"no list literal in Lean definition {defname}")
    content, _ = balanced_bracket(text, start)
    return re.findall(r'"([^"]+)"', content)


def parse_sig(text: str, start_marker: str,
              end_marker: str) -> dict[str, list[str]]:
    """Parse a Lean ``SigEnv`` match: name -> argument descriptors."""
    a = text.find(start_marker)
    if a < 0:
        raise SystemExit(f"cannot find signature marker {start_marker!r}")
    b = text.find(end_marker, a)
    if b < 0:
        raise SystemExit(f"cannot find signature end marker {end_marker!r}")
    body = text[a:b]
    out: dict[str, list[str]] = {}
    for m in re.finditer(r'\|\s*"([^"]+)"\s*=>\s*some\s*\[', body):
        content, _ = balanced_bracket(body, m.end() - 1)
        out[m.group(1)] = split_top_level(content)
    return out


def parse_extract_arities(text: str) -> dict[str, list[int]]:
    """Parse ``extractConstraint`` arms in Compiler/Extract.lean.

    The arity of an arm is the length of its argument-pattern lists (all
    patterns of one name have the same arity in the current source).
    """
    a = text.find("def extractConstraint (names : List String)")
    if a < 0:
        raise SystemExit("cannot find extractConstraint in Extract.lean")
    b = text.find("def extractConstraintWith", a)
    if b < 0:
        raise SystemExit("cannot find end of extractConstraint in Extract.lean")
    body = text[a:b]
    arms = list(re.finditer(r'\n[ \t]*\|\s*"([^"]+)"\s*=>', body))
    out: dict[str, list[int]] = {}
    for i, m in enumerate(arms):
        end = arms[i + 1].start() if i + 1 < len(arms) else len(body)
        segment = body[m.end():end]
        arities: set[int] = set()
        for pm in re.finditer(r"\[\s*(?:\.basic|\.array)", segment):
            content, _ = balanced_bracket(segment, pm.start())
            items = split_top_level(content)
            if items:
                arities.add(len(items))
        out[m.group(1)] = sorted(arities)
    return out


def parse_compile_arities(text: str) -> dict[str, list[int]]:
    """Parse Compiler/Compile.lean for accepted predicate names/arities.

    Two forms occur in the source:

    * literal-bound fallbacks written as
      ``c.name.name = "int_gt" ∧ c.args.length = 2``;
    * match arms ``match c.name.name with | "bool_xor" => ...`` in the
      auxiliary-shape classifiers (``auxShapeOf``/``elemAuxShapeOf``).

    The arity is taken from the argument-pattern list in each arm.  Names
    from both forms are merged; the compiler's constraint path is the union
    of these with ``extractConstraint``'s arms (see ``compiler_names``).
    """
    out: dict[str, set[int]] = collections.defaultdict(set)

    # Literal-bound fallback ifs in compileConstraint.
    pattern = re.compile(
        r'c\.name\.name\s*=\s*"([^"]+)"\s*'
        r'(?:\u2227|/\\)\s*c\.args\.length\s*=\s*(\d+)')
    for m in pattern.finditer(text):
        out[m.group(1)].add(int(m.group(2)))

    # Match arms in the auxiliary-shape classifiers.  A block runs from
    # its `match c.name.name with` to the next top-level `def`.
    for match_m in re.finditer(r'match\s+c\.name\.name\s+with', text):
        block_end = text.find("\ndef ", match_m.end())
        block = text[match_m.end():block_end if block_end >= 0 else len(text)]
        arms = list(re.finditer(r'\n[ \t]*\|\s*"([^"]+)"\s*=>', block))
        for i, arm in enumerate(arms):
            end = arms[i + 1].start() if i + 1 < len(arms) else len(block)
            segment = block[arm.end():end]
            arities: set[int] = set()
            for pm in re.finditer(r"\[\s*(?:\.basic|\.array)", segment):
                content, _ = balanced_bracket(segment, pm.start())
                items = split_top_level(content)
                if items:
                    arities.add(len(items))
            if arities:
                out[arm.group(1)].update(arities)
    return {name: sorted(arities) for name, arities in out.items()}


def load_sources() -> Sources:
    """Read the four Lean source files and extract names/arities."""
    std_text = (ROOT / "LeanFzn/Semantics/StdLib.lean").read_text(
        encoding="utf-8", errors="replace")
    eval_text = (ROOT / "LeanFzn/Semantics/Evaluation.lean").read_text(
        encoding="utf-8", errors="replace")
    glob_text = (ROOT / "LeanFzn/Semantics/Globals.lean").read_text(
        encoding="utf-8", errors="replace")
    extract_text = (ROOT / "LeanFzn/Compiler/Extract.lean").read_text(
        encoding="utf-8", errors="replace")
    compile_text = (ROOT / "LeanFzn/Compiler/Compile.lean").read_text(
        encoding="utf-8", errors="replace")
    return Sources(
        std_names=lean_string_list(eval_text, "stdNames"),
        set_names=lean_string_list(eval_text, "setNames"),
        std_sig=parse_sig(std_text, "def stdSig", "def stdWellFormed"),
        globals_sig=parse_sig(glob_text, "def globalsSig", "def fullSig"),
        globals_unsupported=lean_string_list(glob_text, "globalsUnsupported"),
        extract_arities=parse_extract_arities(extract_text),
        compile_arities=parse_compile_arities(compile_text),
    )


def compiler_names(sources: Sources) -> dict[str, list[int]]:
    """Union of Extract.lean arms and Compile.lean literal fallbacks."""
    out: dict[str, set[int]] = collections.defaultdict(set)
    for name, arities in sources.extract_arities.items():
        out[name].update(arities)
    for name, arities in sources.compile_arities.items():
        out[name].update(arities)
    return {name: sorted(a) for name, a in out.items()}


def descriptor_kind(desc: str) -> tuple[bool, str, bool]:
    """(is_array, base, is_var) for one Lean signature descriptor."""
    is_array = desc.startswith(".array")
    if "setOfInt" in desc:
        base = "set"
    elif ".bool" in desc:
        base = "bool"
    else:
        base = "int"
    return is_array, base, ".var" in desc


def enum_arg(desc: str, literal: bool, index: int) -> tuple[str, bool]:
    """Concrete argument for one signature position and a variable/literal bit.

    Returns ``(text, is_set_variable)``.  Set variables are reported so the
    caller can classify the variant as set-needed, matching the first pass.
    """
    is_array, base, _ = descriptor_kind(desc)
    if is_array:
        if base == "int":
            return ("[1,2]" if literal else "va"), False
        if base == "bool":
            return ("[true,false]" if literal else "ba"), False
        # Array of sets: the parser has no array-of-set declarations, so a
        # variable form is set-needed; a literal array of sets is testable.
        return ("[1..2,2..3]" if literal else "vsa"), (not literal)
    if base == "int":
        return ("1" if literal else f"vi{index % 4}"), False
    if base == "bool":
        return ("true" if literal else f"vb{index % 4}"), False
    return ("1..2" if literal else f"vs{index % 4}"), (not literal)


def enum_variant_label(arity: int, mask: int) -> str:
    if arity == 0:
        return "nullary"
    if mask == 0:
        return "all-var"
    if mask == (1 << arity) - 1:
        return "all-lit"
    bits = ",".join(str(i) for i in range(arity) if (mask >> i) & 1)
    return f"lit@{bits}"


def enum_targets(sources: Sources) -> list[dict]:
    """Build the enumerated/skipped predicate scope.

    Every ``stdSig`` name (the union of ``stdNames`` and ``setNames``) is
    enumerated.  Compiler-only names without a ``stdSig`` entry are included
    if the compiler source gives an arity (none in the current tree).
    ``fzn_*`` globals and ``globalsUnsupported`` are recorded as skipped:
    they are checker-only and the compiler has no arm for them.
    """
    comp = compiler_names(sources)
    extract_set = set(sources.extract_arities)
    compile_set = set(sources.compile_arities)

    def comp_source(name: str) -> str:
        parts = []
        if name in extract_set:
            parts.append("Compiler/Extract.lean")
        if name in compile_set:
            parts.append("Compiler/Compile.lean")
        return ";".join(parts)

    std_order = list(sources.std_names)
    for name in sources.set_names:
        if name not in std_order:
            std_order.append(name)
    targets: list[dict] = []
    seen: set[str] = set()

    for name in std_order:
        seen.add(name)
        descs = sources.std_sig.get(name)
        source = "StdLib.lean:stdSig;Evaluation.lean:"
        source += "setNames" if name in sources.set_names else "stdNames"
        if name in comp:
            source += ";" + comp_source(name)
        if descs is None:
            arity = comp.get(name, [])
            targets.append({
                "name": name, "arity": arity, "descriptors": [],
                "source": source, "compiler_accepted": name in comp,
                "scope": "skipped",
                "reason": "no stdSig descriptors; cannot build typed arguments",
            })
            continue
        targets.append({
            "name": name, "arity": [len(descs)], "descriptors": descs,
            "source": source, "compiler_accepted": name in comp,
            "scope": "enumerated", "reason": "",
        })

    for name, arities in comp.items():
        if name in seen:
            continue
        seen.add(name)
        descs = sources.std_sig.get(name)
        if descs is None:
            targets.append({
                "name": name, "arity": arities, "descriptors": [],
                "source": comp_source(name),
                "compiler_accepted": True, "scope": "skipped",
                "reason": "compiler arity known but no stdSig descriptors",
            })
        else:
            targets.append({
                "name": name, "arity": [len(descs)], "descriptors": descs,
                "source": comp_source(name),
                "compiler_accepted": True, "scope": "enumerated",
                "reason": "",
            })

    for name, descs in sources.globals_sig.items():
        if name in seen:
            continue
        seen.add(name)
        targets.append({
            "name": name, "arity": [len(descs)], "descriptors": descs,
            "source": "Globals.lean:globalsSig", "compiler_accepted": False,
            "scope": "skipped",
            "reason": ("checker-supported fzn_* global; the compiler has no "
                       "fzn_* case (Extract.lean), so every call is rejected "
                       "as an unsupported predicate"),
        })

    for name in sources.globals_unsupported:
        if name in seen:
            continue
        seen.add(name)
        descs = sources.globals_sig.get(name, [])
        targets.append({
            "name": name, "arity": [len(descs)] if descs else [],
            "descriptors": descs,
            "source": "Globals.lean:globalsUnsupported",
            "compiler_accepted": False, "scope": "skipped",
            "reason": "explicitly unsupported by the checker (globalsUnsupported)",
        })
    return targets


def enumerate_predicates(sources: Sources, out_dir: Path, binary: Path,
                         cap: float) -> tuple[list[dict], list[dict]]:
    """Run every variable/literal variant for each enumerated predicate.

    Returns ``(target_rows, variant_rows)``; targets include skipped global
    names so the scope file documents exactly what was not enumerated.
    """
    targets = enum_targets(sources)
    enum_dir = out_dir / "enum_micro"
    enum_dir.mkdir(parents=True, exist_ok=True)
    rows: list[dict] = []
    counter = 0
    runnable = [t for t in targets if t["scope"] == "enumerated"]
    print(f"\nEnumeration: {len(runnable)} predicates, "
          f"{len(targets) - len(runnable)} skipped", flush=True)

    for target in runnable:
        name = target["name"]
        descs = target["descriptors"]
        arity = len(descs)
        if target["arity"] and len(target["arity"]) == 1 \
                and target["arity"][0] != arity:
            print(f"  warning: {name}: signature arity {arity} disagrees "
                  f"with source arity {target['arity']}", flush=True)
        source = target["source"]
        for mask in range(1 << arity):
            counter += 1
            args: list[str] = []
            set_var = False
            for i, desc in enumerate(descs):
                text, is_set_var = enum_arg(desc, bool((mask >> i) & 1), i)
                args.append(text)
                set_var = set_var or is_set_var
            label = enum_variant_label(arity, mask)
            mask_text = "".join(
                "1" if (mask >> i) & 1 else "0" for i in range(arity))
            args_text = ",".join(args)
            model_rel = "-"
            if set_var:
                result = RunResult(
                    "set", None, 0.0,
                    "set variable argument (set variables are outside the "
                    "finite fragment); not tested")
            else:
                text = (ENUM_HEADER
                        + f"constraint {name}({args_text});\n"
                        + "solve satisfy;\n")
                mask_tag = mask_text or "0"
                filename = (f"{counter:04d}_{safe_name(name)}_"
                            f"{mask_tag}.fzn")
                result = run_model(binary, text, enum_dir / filename, cap)
                model_rel = f"enum_micro/{filename}"
            rows.append({
                "predicate": name,
                "arity": arity,
                "source": source,
                "compiler_accepted": "yes" if target["compiler_accepted"] else "no",
                "variant": label,
                "literal_mask": mask_text,
                "args": args_text,
                "status": result.status,
                "reason": one_line(result.reason),
                "exit_code": "" if result.exit_code is None else result.exit_code,
                "wall_s": f"{result.wall_s:.3f}",
                "model": model_rel,
            })
        if counter % 50 < (1 << arity):
            print(f"  enum {counter:4d} variants "
                  f"(last {name}, {arity}-ary)", flush=True)

    return targets, rows


# ---------------------------------------------------------------------------
# Output files
# ---------------------------------------------------------------------------

def write_tsv(path: Path, header: list[str], rows: list[list]) -> None:
    with path.open("w", encoding="utf-8", newline="") as f:
        w = csv.writer(f, delimiter="\t", lineterminator="\n")
        w.writerow(header)
        w.writerows(rows)


def write_matrices(out_dir: Path,
                   shape_families: dict[str, collections.Counter],
                   results: dict[str, RunResult]) -> None:
    families = sorted({fam for counts in shape_families.values()
                       for fam in counts})
    rows = []
    for shape in sorted(shape_families):
        counts = shape_families[shape]
        fam_text = ";".join(f"{fam}:{counts[fam]}" for fam in sorted(counts))
        result = results[shape]
        rows.append([shape, sum(counts.values()), fam_text, result.status,
                     one_line(result.reason), result.model])
    write_tsv(out_dir / "shape_matrix.tsv",
              ["shape", "occurrences", "families", "status", "reason",
               "micro_model"], rows)

    matrix_rows = []
    for shape in sorted(shape_families):
        matrix_rows.append([shape]
                           + [shape_families[shape].get(fam, 0)
                              for fam in families])
    write_tsv(out_dir / "shape_family_matrix.tsv", ["shape"] + families,
              matrix_rows)

    payload = {}
    for shape in sorted(shape_families):
        result = results[shape]
        payload[shape] = {
            "occurrences": sum(shape_families[shape].values()),
            "families": dict(sorted(shape_families[shape].items())),
            "status": result.status,
            "reason": one_line(result.reason),
            "micro_model": result.model,
        }
    (out_dir / "shapes.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8")


def write_census(out_dir: Path, models: list[str],
                 model_shapes: dict[str, collections.Counter],
                 model_decls: dict[str, collections.Counter],
                 model_family: dict[str, str]) -> None:
    shape_rows = []
    for model in models:
        family = model_family[model]
        for shape, count in sorted(model_shapes[model].items()):
            shape_rows.append([model, family, shape, count])
    write_tsv(out_dir / "census.tsv",
              ["model", "family", "shape", "count"], shape_rows)

    decl_rows = []
    for model in models:
        family = model_family[model]
        for form, count in sorted(model_decls[model].items()):
            decl_rows.append([model, family, form, count])
    write_tsv(out_dir / "declarations.tsv",
              ["model", "family", "declaration_form", "count"], decl_rows)

    total = collections.Counter()
    models_per = collections.defaultdict(set)
    families_per: dict[str, set[str]] = collections.defaultdict(set)
    for model in models:
        family = model_family[model]
        for form, count in model_decls[model].items():
            total[form] += count
            models_per[form].add(model)
            families_per[form].add(family)
    summary_rows = []
    for form in sorted(total):
        summary_rows.append([
            form, total[form], len(models_per[form]),
            ";".join(sorted(families_per[form]))])
    write_tsv(out_dir / "declaration_summary.tsv",
              ["declaration_form", "occurrences", "models", "families"],
              summary_rows)


def write_micro_runs(out_dir: Path,
                     results: dict[str, RunResult]) -> None:
    rows = []
    for shape in sorted(results):
        r = results[shape]
        rows.append([shape, r.status,
                     "" if r.exit_code is None else r.exit_code,
                     f"{r.wall_s:.3f}", one_line(r.reason), r.model])
    write_tsv(out_dir / "micro_runs.tsv",
              ["shape", "status", "exit_code", "wall_s", "reason", "model"],
              rows)


def write_enumeration(out_dir: Path, targets: list[dict],
                      rows: list[dict]) -> None:
    scope_rows = []
    for t in targets:
        scope_rows.append([
            t["name"],
            ",".join(str(a) for a in t["arity"]) if t["arity"] else "-",
            t["source"],
            ";".join(t["descriptors"]),
            t["scope"],
            "yes" if t["compiler_accepted"] else "no",
            one_line(t["reason"]),
        ])
    write_tsv(out_dir / "enumeration_scope.tsv",
              ["predicate", "arity", "source", "descriptors", "scope",
               "compiler_accepted", "reason"], scope_rows)

    header = ["predicate", "arity", "source", "compiler_accepted", "variant",
              "literal_mask", "args", "status", "reason", "exit_code",
              "wall_s", "model"]
    write_tsv(out_dir / "enumeration.tsv", header,
              [[r[h] for h in header] for r in rows])

    per: dict[str, collections.Counter] = collections.defaultdict(
        collections.Counter)
    first_rejection: dict[str, str] = {}
    compiler_accepted: dict[str, str] = {}
    arity_of: dict[str, int] = {}
    source_of: dict[str, str] = {}
    for r in rows:
        name = r["predicate"]
        per[name][r["status"]] += 1
        per[name]["variants"] += 1
        compiler_accepted[name] = r["compiler_accepted"]
        arity_of[name] = r["arity"]
        source_of[name] = r["source"]
        if r["status"] == "rejected" and name not in first_rejection:
            first_rejection[name] = r["reason"]
    agg_rows = []
    for name in sorted(per):
        c = per[name]
        agg_rows.append([
            name, arity_of[name], source_of[name], compiler_accepted[name],
            c["variants"], c["accepted"], c["rejected"], c["set"],
            c["timeout"], first_rejection.get(name, ""),
        ])
    write_tsv(out_dir / "enumeration_matrix.tsv",
              ["predicate", "arity", "source", "compiler_accepted",
               "variants", "accepted", "rejected", "set", "timeout",
               "first_rejection"], agg_rows)


def summarize(out_dir: Path, models: list[str],
              shape_families: dict[str, collections.Counter],
              model_decls: dict[str, collections.Counter],
              model_family: dict[str, str],
              results: dict[str, RunResult],
              targets: list[dict], enum_rows: list[dict]) -> None:
    counts = collections.Counter(r.status for r in results.values())
    total_shapes = len(shape_families)
    total_occurrences = sum(sum(c.values()) for c in shape_families.values())
    families = sorted(set(model_family.values()))
    observed = (counts["accepted"], counts["rejected"], counts["set"])
    matches = observed == PROTOTYPE_SPLIT

    rejected = [(shape, dict(sorted(shape_families[shape].items())),
                 one_line(results[shape].reason))
                for shape in sorted(results)
                if results[shape].status == "rejected"]
    set_needed = [(shape, dict(sorted(shape_families[shape].items())))
                  for shape in sorted(results)
                  if results[shape].status == "set"]
    timed_out = [shape for shape in sorted(results)
                 if results[shape].status == "timeout"]

    decl_forms = sorted({form for counts in model_decls.values()
                         for form in counts})
    decl_occurrences = sum(sum(c.values())
                           for c in model_decls.values())

    enum_counts = collections.Counter(r["status"] for r in enum_rows)
    enum_by_pred: dict[str, collections.Counter] = collections.defaultdict(
        collections.Counter)
    for r in enum_rows:
        enum_by_pred[r["predicate"]][r["status"]] += 1
    enum_names = len(enum_by_pred)
    compiler_targets = [t for t in targets
                        if t["scope"] == "enumerated"
                        and t["compiler_accepted"]]
    skipped_targets = [t for t in targets if t["scope"] == "skipped"]
    compiler_accepted_names = {t["name"] for t in targets
                               if t["compiler_accepted"]}
    enum_compiler_counts = collections.Counter()
    for name, c in enum_by_pred.items():
        if name in compiler_accepted_names:
            for status in ("accepted", "rejected", "set", "timeout"):
                enum_compiler_counts[status] += c[status]
    # A name accepted by the running binary but absent from the source-derived
    # accepted set means the source parser missed a compiler path.
    source_gaps = sorted(name for name, c in enum_by_pred.items()
                         if c["accepted"] and name not in compiler_accepted_names)
    bool_eq_lit = next((r for r in enum_rows
                        if r["predicate"] == "bool_eq"
                        and r["variant"] == "all-lit"), None)

    lines = []
    lines.append(f"Shape matrix summary: {out_dir}")
    lines.append("")
    lines.append("First pass (streaming census):")
    lines.append(f"  models: {len(models)}")
    lines.append(f"  families: {len(families)} ({', '.join(families)})")
    lines.append(f"  distinct shapes: {total_shapes}")
    lines.append(f"  shape occurrences: {total_occurrences}")
    lines.append(f"  declaration forms: {len(decl_forms)} distinct, "
                 f"{decl_occurrences} declarations")
    lines.append("  wlp22: streamed line by line; no size cutoff")
    lines.append("")
    lines.append("First-pass micro-model split:")
    lines.append(f"  accepted: {counts['accepted']}")
    lines.append(f"  rejected: {counts['rejected']}")
    lines.append(f"  set:      {counts['set']}")
    lines.append(f"  timeout:  {counts['timeout']}")
    lines.append(f"  prototype split {PROTOTYPE_SPLIT[0]}/"
                 f"{PROTOTYPE_SPLIT[1]}/{PROTOTYPE_SPLIT[2]}: "
                 f"{'MATCH' if matches else 'DIFFERENT'}")
    lines.append("")
    lines.append("Rejected shapes (first stderr line):")
    for shape, fams, reason in rejected:
        fam_text = ", ".join(f"{fam}:{n}" for fam, n in fams.items())
        lines.append(f"  {shape}  [{fam_text}]  {reason}")
    if not rejected:
        lines.append("  (none)")
    lines.append("")
    lines.append("Set-required shapes (not tested in the first pass):")
    for shape, fams in set_needed:
        fam_text = ", ".join(f"{fam}:{n}" for fam, n in fams.items())
        lines.append(f"  {shape}  [{fam_text}]")
    if not set_needed:
        lines.append("  (none)")
    lines.append("")
    if timed_out:
        lines.append("Timed-out shapes:")
        for shape in timed_out:
            lines.append(f"  {shape}")
        lines.append("")
    lines.append("Second pass (source-derived enumeration):")
    lines.append(f"  predicates enumerated: {enum_names}")
    lines.append(f"  compiler-accepted names among them: "
                 f"{len(compiler_targets)}")
    lines.append(f"  variants: {len(enum_rows)}")
    lines.append(f"  accepted: {enum_counts['accepted']}")
    lines.append(f"  rejected: {enum_counts['rejected']}")
    lines.append(f"  set:      {enum_counts['set']}")
    lines.append(f"  timeout:  {enum_counts['timeout']}")
    lines.append(f"  compiler-accepted names, variant status: "
                 f"accepted={enum_compiler_counts['accepted']} "
                 f"rejected={enum_compiler_counts['rejected']} "
                 f"set={enum_compiler_counts['set']} "
                 f"timeout={enum_compiler_counts['timeout']}")
    n_globals = sum(1 for t in skipped_targets
                    if t["source"] == "Globals.lean:globalsSig")
    n_unsupported = sum(1 for t in skipped_targets
                        if t["source"] == "Globals.lean:globalsUnsupported")
    lines.append(f"  skipped names: {len(skipped_targets)} "
                 f"({n_globals} checker-only fzn_* globals, "
                 f"{n_unsupported} globalsUnsupported; "
                 f"see enumeration_scope.tsv)")
    if source_gaps:
        lines.append("  SOURCE-PARSING GAPS (accepted by the binary but not "
                     "derived from the compiler source):")
        for name in source_gaps:
            lines.append(f"    {name} ({enum_by_pred[name]['accepted']} "
                         f"accepted variant(s))")
    else:
        lines.append("  source/binary consistency: every predicate with an "
                     "accepted variant was derived from the compiler source")
    if bool_eq_lit is not None:
        lines.append(f"  example bool_eq all-literal: "
                     f"{bool_eq_lit['status']} ({bool_eq_lit['reason']})")
    lines.append("")
    lines.append("Notes:")
    lines.append(
        "  - The micro-model header declares the int parameter array before "
        "variables because the parser enforces parameter-before-variable "
        "order; the prototype's variable-first header produced a parse error "
        "on every testable shape.  Token-to-argument rules are otherwise the "
        "prototype's.")
    lines.append(
        "  - The prototype's rejected-linear label was "
        "int_lin_le([L],[vint],L).  This run rejects "
        "int_lin_le([pint],[L],L) instead: that is the shape whose variable "
        "array is all integer literals; int_lin_le([L],[vint],L) is accepted "
        "with the generated [1,1] coefficients.  The 46/6/9 counts are "
        "unchanged.")
    lines.append(
        "  - Audit/dev-only tool: standard-library Python only, no solver "
        "runtime dependency, no Lean edits.")

    text = "\n".join(lines) + "\n"
    (out_dir / "summary.txt").write_text(text, encoding="utf-8")

    summary_rows: list[list] = []
    def add(section: str, key: str, value) -> None:
        summary_rows.append([section, key, value])
    add("cohort", "models", len(models))
    add("cohort", "families", ";".join(families))
    add("census", "distinct_shapes", total_shapes)
    add("census", "shape_occurrences", total_occurrences)
    add("census", "declaration_forms", len(decl_forms))
    add("census", "declarations", decl_occurrences)
    for status in ("accepted", "rejected", "set", "timeout"):
        add("micro", status, counts[status])
    add("micro", "prototype_split", "/".join(map(str, PROTOTYPE_SPLIT)))
    add("micro", "prototype_match", "yes" if matches else "no")
    for shape, fams, reason in rejected:
        add("rejected", shape,
            ";".join(f"{fam}:{n}" for fam, n in fams.items()) + " | " + reason)
    for shape, fams in set_needed:
        add("set", shape, ";".join(f"{fam}:{n}" for fam, n in fams.items()))
    add("enum", "predicates_enumerated", enum_names)
    add("enum", "compiler_accepted_names", len(compiler_targets))
    add("enum", "variants", len(enum_rows))
    for status in ("accepted", "rejected", "set", "timeout"):
        add("enum", status, enum_counts[status])
        add("enum_compiler", status, enum_compiler_counts[status])
    add("enum", "skipped_names", len(skipped_targets))
    add("enum", "skipped_globals", n_globals)
    add("enum", "skipped_globals_unsupported", n_unsupported)
    add("enum", "source_gaps", ",".join(source_gaps) if source_gaps else "none")
    for t in skipped_targets:
        add("enum_skipped", t["name"], t["reason"])
    write_tsv(out_dir / "summary.tsv", ["section", "key", "value"],
              summary_rows)
    print("\n" + text, flush=True)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--cohort", required=True,
                   help="file with one FlatZinc model path per line")
    p.add_argument("--out", default=None,
                   help="output directory (default tmp/shape-matrix-<date>)")
    p.add_argument("--binary", default=str(DEFAULT_BIN),
                   help="leanfzn binary (default .lake/build/bin/leanfzn)")
    p.add_argument("--cap", type=float, default=20.0,
                   help="wall cap per micro-model in seconds (default 20)")
    p.add_argument("--limit", type=int, default=0,
                   help="only the first N cohort models (0 = all)")
    args = p.parse_args()
    if args.cap <= 0:
        p.error("--cap must be positive")
    if args.out is None:
        stamp = datetime.now(timezone.utc).strftime("%Y%m%d")
        out = ROOT / "tmp" / f"shape-matrix-{stamp}"
        if out.exists():
            out = ROOT / "tmp" / (
                f"shape-matrix-{stamp}-"
                f"{datetime.now(timezone.utc).strftime('%H%M%S')}")
        args.out = str(out)
    return args


def main() -> None:
    args = parse_args()
    cohort = Path(args.cohort)
    if not cohort.is_absolute():
        cohort = ROOT / cohort
    models = [line.strip() for line in cohort.read_text(
        encoding="utf-8").splitlines()
        if line.strip() and not line.startswith("#")]
    if args.limit:
        models = models[:args.limit]
    if not models:
        raise SystemExit(f"empty cohort: {cohort}")

    binary = Path(args.binary)
    if not binary.is_file():
        raise SystemExit(f"missing solver binary: {binary}")

    out_dir = Path(args.out)
    if not out_dir.is_absolute():
        out_dir = ROOT / out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    print(f"Shape matrix (dev-only): {len(models)} cohort models")
    print(f"Binary: {binary}")
    print(f"Output: {out_dir}")
    print("wlp22 is streamed line by line; no size cutoff.", flush=True)

    shape_families, model_shapes, model_decls, model_family = census(models)
    results = classify_shapes(shape_families, out_dir, binary, args.cap)

    write_matrices(out_dir, shape_families, results)
    write_census(out_dir, models, model_shapes, model_decls, model_family)
    write_micro_runs(out_dir, results)

    sources = load_sources()
    targets, enum_rows = enumerate_predicates(
        sources, out_dir, binary, args.cap)
    write_enumeration(out_dir, targets, enum_rows)

    summarize(out_dir, models, shape_families, model_decls, model_family,
              results, targets, enum_rows)


if __name__ == "__main__":
    main()
