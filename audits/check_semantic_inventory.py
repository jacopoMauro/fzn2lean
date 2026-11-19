#!/usr/bin/env python3
"""Check review coverage and freshness, not mathematical semantic equivalence.

Run from any directory. --upstream-root optionally verifies the downloaded
libminizinc tree against the immutable upstream evidence hashes. --require-clean
fails when the reviewed inventory contains unresolved conformance findings.
Review decisions must be made explicitly; this tool never stamps them approved.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
INVENTORY = ROOT / 'specification/minizinc-2.10.1/semantic_conformance.json'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def without_comments(source):
    """Remove nested Lean/MiniZinc block and line comments; preserve strings."""
    out = list(source)
    i, depth, quoted = 0, 0, False
    while i < len(source):
        if depth:
            if source.startswith('/-', i) or source.startswith('/*', i):
                out[i:i + 2] = '  '; depth += 1; i += 2
            elif source.startswith('-/', i) or source.startswith('*/', i):
                out[i:i + 2] = '  '; depth -= 1; i += 2
            else:
                if source[i] != '\n': out[i] = ' '
                i += 1
        elif quoted:
            if source[i] == '\\': i += 2
            else:
                if source[i] == '"': quoted = False
                i += 1
        elif source.startswith('/-', i) or source.startswith('/*', i):
            out[i:i + 2] = '  '; depth = 1; i += 2
        elif source.startswith('--', i) or source[i] == '%':
            while i < len(source) and source[i] != '\n':
                out[i] = ' '; i += 1
        else:
            if source[i] == '"': quoted = True
            i += 1
    return ''.join(out)


def signature_lists(text):
    """Parse a Lean list-of-signatures literal at the start of `text`.

    `SigEnv` maps a name to a *list* of parameter-type lists, so a
    `stdSig`/`globalsSig` case is `| "name" => [[...], [...]]`.  Each
    signature is rendered exactly as its inner `[...]` source text,
    stripped.  A bracket-depth scanner is used instead of a regular
    expression because a signature list contains commas and parentheses,
    and the outer list contains one `[...]` per overload.
    """
    i = len(text) - len(text.lstrip())
    if i >= len(text) or text[i] != '[':
        return None
    sigs = []
    depth = 0
    start = None
    while i < len(text):
        char = text[i]
        if char == '[':
            depth += 1
            if depth == 2:
                start = i
        elif char == ']':
            if depth == 2 and start is not None:
                sigs.append(text[start:i + 1].strip())
                start = None
            depth -= 1
            if depth == 0:
                return sigs
        i += 1
    return None


def signature_cases(path, start, end):
    source = without_comments(path.read_text())
    chunk = source.split('def ' + start, 1)[1].split('def ' + end, 1)[0]
    cases = {}
    for match in re.finditer(r'\| "([^"]+)"\s*=>', chunk):
        sigs = signature_lists(chunk[match.end():])
        if sigs is not None:
            cases[match.group(1)] = sigs
    return cases


def normalised_signatures(value):
    """Accept the pre-H1 `lean_signature` string as a one-signature list.

    The reviewed JSON still stores the old single-signature rendering.
    Interpretation as a singleton list keeps the comparison strict while
    the inventory is converted to the list-of-signatures schema.
    """
    return [value] if isinstance(value, str) else value


def active_signatures(root=ROOT):
    return {
        **signature_cases(root / 'LeanFzn/Semantics/StdLib.lean', 'stdSig', 'stdWellFormed'),
        **signature_cases(root / 'LeanFzn/Semantics/Globals.lean', 'globalsSig', 'fullSig'),
    }


def published_builtins(root=ROOT):
    names = set()
    for path in (root / 'specification/minizinc-2.10.1').glob('lib-flatzinc-*.html'):
        names.update(re.findall(r'<h2>(\w+)<', path.read_text()))
    return names


def excluded_globals(root=ROOT):
    source = without_comments((root / 'LeanFzn/Semantics/Globals.lean').read_text())
    block = source.split('def globalsUnsupported', 1)[1].split(']', 1)[0]
    return set(re.findall(r'"([^"]+)"', block))


def check(data, root=ROOT, upstream_root=None, require_clean=False):
    errors = []
    if data.get('upstream_commit') != 'c3448c48e7f05f13805616cfd1b9e94972eef58c':
        errors.append('unexpected upstream commit; upgrade requires a new review')
    entries = data['predicates']
    names = [r['name'] for r in entries]
    if len(names) != len(set(names)): errors.append('duplicate predicate review rows')
    actual = active_signatures(root)
    reviewed = {r['name'] for r in entries if r['implemented']}
    if reviewed != set(actual):
        errors.append(f'signature coverage differs: missing={sorted(set(actual)-reviewed)}, '
                      f'extra={sorted(reviewed-set(actual))}')
    missing_builtins = published_builtins(root) - set(names)
    if missing_builtins:
        errors.append(f'published builtin/function rows missing: {sorted(missing_builtins)}')
    missing_excluded = excluded_globals(root) - set(names)
    if missing_excluded:
        errors.append(f'explicitly excluded global rows missing: {sorted(missing_excluded)}')
    statuses = {'reviewed', 'restricted', 'extension', 'nonconformant', 'unsupported'}
    findings = {r['id']: r for r in data['findings']}
    for r in entries:
        name = r['name']
        if r.get('status') not in statuses: errors.append(f'{name}: invalid review status')
        for field in ('contract', 'edge_cases', 'signature_review', 'source', 'implementation'):
            if not r.get(field): errors.append(f'{name}: missing {field}')
        if r['implemented'] and normalised_signatures(r['lean_signature']) != actual.get(name):
            errors.append(f'{name}: signature changed since review')
        for finding in r.get('findings', []):
            if finding not in findings: errors.append(f'{name}: unknown finding {finding}')
            elif name not in findings[finding]['predicates']:
                errors.append(f'{name}: finding {finding} does not cover this predicate')
            elif findings[finding]['state'] == 'open' and r['status'] in {'reviewed', 'extension'}:
                errors.append(f'{name}: unresolved finding cannot be marked reviewed')
        if r['status'] == 'nonconformant' and not r.get('findings'):
            errors.append(f'{name}: nonconformance requires a finding')
    # A clean review must not hide an unchecked admitted-input premise.
    admission_source = root / 'LeanFzn/Semantics/Admission.lean'
    admission_text = without_comments(admission_source.read_text()) if admission_source.is_file() else ''
    for row in entries:
        if row['status'] != 'restricted':
            continue
        name = row['name']
        contract = row.get('admission', {})
        if contract.get('policy') not in {'runtime_gate', 'excluded'}:
            errors.append(f'{name}: missing explicit admission policy')
        for field in ('scope', 'review_basis', 'gate', 'theorems', 'regressions',
                      'checker_scope', 'solver_scope'):
            if not contract.get(field):
                errors.append(f'{name}: admission missing {field}')
        if '"' + name + '"' not in admission_text:
            errors.append(f'{name}: absent from runtime admission dispatch')
        gate_path = contract.get('gate', '').split(':')[0]
        if gate_path and not (root / gate_path).is_file():
            errors.append(f'{name}: admission gate file missing')
        for path in contract.get('regressions', []):
            if not (root / path).is_file():
                errors.append(f'{name}: admission regression missing: {path}')
    for finding in data['findings']:
        if finding['state'] not in {'open', 'fixed'}:
            errors.append(f"{finding['id']}: invalid finding state")
        for name in finding['predicates']:
            rows = [r for r in entries if r['name'] == name]
            if len(rows) != 1 or finding['id'] not in rows[0]['findings']:
                errors.append(f"{finding['id']}: missing reverse link for {name}")
    required = {str(p.relative_to(root)) for p in
                (root / 'LeanFzn/Semantics').rglob('*.lean')}
    required.update({'LeanFzn/Syntax/AST.lean', 'LeanFzn/Parser/Grammar.lean',
                     'LeanFzn/Checker/Runtime/Check.lean',
                     'LeanFzn/Checker/Runtime/Solution.lean',
                     'LeanFzn/Integration/Config/Annotations.lean',
                     'LeanFzn/Compiler/Normalize.lean',
                     'LeanFzn/Checker/Proofs/Check.lean',
                     'LeanFzn/Integration/Public/PhaseStats.lean',
                     'LeanFzn/Integration/Public/Driver.lean',
                     'Tests/Cli/test_admission.py',
                     'Tests/Semantics/Admission.lean',
                     'Tests/Compiler/AdmissionTest.lean',
                     'Tests/Checker/Fast.lean',
                     'Tests/Semantics/ConformanceT10Counting.lean',
                     'lean-toolchain', 'lake-manifest.json'})
    # Lexical certification is now a source contract, not an unchecked lexer
    # hidden inside ValidFlatZinc. Keep its specification/implementation and
    # public proof endpoints tied to reviewed evidence as well.
    required.update({'LeanFzn/Parser/Token.lean', 'LeanFzn/Parser/Lexical.lean',
                     'LeanFzn/Parser/Lexer.lean',
                     'LeanFzn/Parser/Proofs/LexerCorrectness.lean',
                     'LeanFzn/Parser/Proofs/SourceCorrectness.lean',
                     'Tests/Parser/LexicalSpec.lean'})
    if required - data['reviewed_files'].keys():
        errors.append(f"missing reviewed source hashes: {sorted(required-data['reviewed_files'].keys())}")
    for path, expected in data['reviewed_files'].items():
        p = root / path
        if not p.is_file() or digest(p) != expected:
            errors.append(f'{path}: review is stale (content hash changed or file missing)')
    for evidence in data['upstream_evidence']:
        if upstream_root is not None:
            p = Path(upstream_root) / evidence['path']
            if not p.is_file() or digest(p) != evidence['sha256']:
                errors.append(f"upstream evidence mismatch: {evidence['path']}")
    if not data.get('model_rules'): errors.append('missing declaration/model-rule review')
    for row in data.get('model_rules', []):
        if row.get('status') == 'restricted':
            admission = row.get('admission', {})
            if admission.get('policy') != 'typing_and_runtime_gate' or not all(
                    admission.get(key) for key in ('gate', 'typing', 'regressions')):
                errors.append(f"{row['id']}: missing model admission evidence")
    if require_clean:
        for finding in data['findings']:
            if finding['state'] == 'open': errors.append(f"open finding: {finding['id']}")
    return errors


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--upstream-root', type=Path)
    parser.add_argument('--require-clean', action='store_true')
    args = parser.parse_args()
    data = json.loads(INVENTORY.read_text())
    errors = check(data, upstream_root=args.upstream_root, require_clean=args.require_clean)
    counts = Counter(r['status'] for r in data['predicates'])
    print(f"Semantic inventory: {len(active_signatures())} implemented names; "
          f"{len(data['predicates'])} review rows; {dict(sorted(counts.items()))}")
    print('This validates coverage/provenance/freshness; it does not prove conformance.')
    for error in errors: print('ERROR:', error, file=sys.stderr)
    return bool(errors)


if __name__ == '__main__':
    raise SystemExit(main())
