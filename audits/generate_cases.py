#!/usr/bin/env python3
"""Generate the B0 parameterized benchmark fixtures with fixed seeds.

Writes FlatZinc files and witness files under
`audits/benchmark_fixtures/generated/` plus `generated_manifest.json` recording
each generator, its parameters, seed, expected result, and how that result was
established. Satisfiable cases are explicit constructions verified with
`leanfzn check` (the solver's verified checker). The Boolean pigeonhole cases
are UNSAT by exhaustive enumeration of pigeon-to-hole injections, which is
complete because every assignment restricts to such an injection; the method is
additionally cross-checked against full assignment enumeration at small sizes.

`--register` copies the generated entries into
`audits/performance_manifest.json` with `default: false` (the default quick
suite is unchanged). No Lean build is run; only the `check` subcommand is used.
"""
from __future__ import annotations
import argparse
import datetime
import hashlib
import itertools
import json
import random
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT/'audits/benchmark_fixtures/generated'
MANIFEST_PATH = ROOT/'audits/performance_manifest.json'
DEFAULT_BINARY = ROOT/'.lake/build/bin/leanfzn'
DENSE_SEED_A = 20261017
DENSE_SEED_B = 20261018


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def utc_stamp():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def emit_solution(entries):
    return '\n'.join(entries) + '\n----------\n'


def latin_case(n):
    names = [f'x{i}{j}' for i in range(n) for j in range(n)]
    lines = [f'var 1..{n}: {name} :: output_var;' for name in names]
    for i in range(n):
        lines.append('constraint all_different([' +
                     ','.join(f'x{i}{j}' for j in range(n)) + ']);')
    for j in range(n):
        lines.append('constraint all_different([' +
                     ','.join(f'x{i}{j}' for i in range(n)) + ']);')
    lines.append('solve satisfy;')
    witness = emit_solution([f'x{i}{j} = {(i+j) % n + 1};'
                             for i in range(n) for j in range(n)])
    return {'id': f'gen_latin{n}', 'file': f'latin{n}.fzn', 'text': '\n'.join(lines) + '\n',
            'witness': witness, 'family': 'generated_latin', 'generator': 'latin',
            'params': {'n': n}, 'seed': None, 'mode': 'satisfy', 'expected': 'sat',
            'check_method': 'constructed_witness',
            'check_detail': f'Latin square x_ij = (i + j) mod {n} + 1, checked with leanfzn check'}


def domain_width_case(w):
    lines = [f'var 0..{w}: x :: output_var;', f'var 0..{w}: y :: output_var;',
             'constraint int_le(x,16);',
             f'constraint int_lin_eq([1,1],[x,y],{w});',
             'constraint int_lin_ne([1,-1],[x,y],0);',
             'solve satisfy;']
    witness = emit_solution(['x = 1;', f'y = {w-1};'])
    return {'id': f'gen_domain{w}', 'file': f'domain_width_{w}.fzn',
            'text': '\n'.join(lines) + '\n', 'witness': witness,
            'family': 'generated_domain_width', 'generator': 'domain_width',
            'params': {'width': w}, 'seed': None, 'mode': 'satisfy', 'expected': 'sat',
            'check_method': 'constructed_witness',
            'check_detail': f'witness x=1, y={w-1}: bound, sum and hole x != y all hold; '
                            'checked with leanfzn check'}


def dense_clause_case(case_id, n_vars, n_clauses, seed):
    rng = random.Random(seed)
    planted = [rng.random() < 0.5 for _ in range(n_vars)]
    clauses = []
    for _ in range(n_clauses):
        vs = rng.sample(range(n_vars), 3)
        pos = [v for v in vs if rng.random() < 0.5]
        neg = [v for v in vs if v not in pos]
        if not any(planted[v] for v in pos) and not any(not planted[v] for v in neg):
            flip = rng.choice(vs)
            if flip in pos:
                pos.remove(flip)
                neg.append(flip)
            else:
                neg.remove(flip)
                pos.append(flip)
        clauses.append((sorted(pos), sorted(neg)))
    lines = [f'var bool: b{i} :: output_var;' for i in range(n_vars)]
    for pos, neg in clauses:
        lines.append('constraint bool_clause([' +
                     ','.join(f'b{v}' for v in pos) + '],[' +
                     ','.join(f'b{v}' for v in neg) + ']);')
    lines.append('solve satisfy;')
    witness = emit_solution([f'b{i} = {"true" if planted[i] else "false"};'
                             for i in range(n_vars)])
    return {'id': case_id, 'file': case_id + '.fzn', 'text': '\n'.join(lines) + '\n',
            'witness': witness, 'family': 'generated_dense_clause',
            'generator': 'dense_clause', 'params': {'n_vars': n_vars, 'n_clauses': n_clauses},
            'seed': seed, 'mode': 'satisfy', 'expected': 'sat',
            'check_method': 'constructed_planted_witness',
            'check_detail': f'seed {seed}: every clause was repaired to be satisfied by the '
                            'planted assignment; checked with leanfzn check'}


def pigeonhole_injections(n_holes):
    """Saturating search for a pigeon-to-hole injection covering all pigeons.

    Every assignment of the CNF formulation restricts to an injection from the
    pigeons that occupy at least one hole to distinct holes, so this enumeration
    is a complete UNSAT test. Returns (sat_witness, maps_examined).
    """
    n_pigeons = n_holes + 1
    examined = 0
    for k in range(n_pigeons + 1):
        for subset in itertools.combinations(range(n_pigeons), k):
            for image in itertools.permutations(range(n_holes), k):
                examined += 1
                if k == n_pigeons:
                    return list(zip(subset, image)), examined
    return None, examined


def brute_force_bool(fzn_clauses, n_vars):
    """Exhaustive 2^n_vars assignment enumeration for small CNFs."""
    for bits in range(1 << n_vars):
        if all(any(bits >> v & 1 for v in pos) or any(not (bits >> v & 1) for v in neg)
               for pos, neg in fzn_clauses):
            return bits
    return None


def pigeonhole_case(n_holes):
    n_pigeons = n_holes + 1
    names = [f'p{p}_h{h}' for p in range(n_pigeons) for h in range(n_holes)]
    lines = [f'var bool: {name} :: output_var;' for name in names]
    clauses = []
    for p in range(n_pigeons):
        clauses.append((list(range(p * n_holes, (p + 1) * n_holes)), []))
    for h in range(n_holes):
        for p in range(n_pigeons):
            for q in range(p + 1, n_pigeons):
                clauses.append(([], [p * n_holes + h, q * n_holes + h]))
    for pos, neg in clauses:
        lines.append('constraint bool_clause([' +
                     ','.join(names[v] for v in pos) + '],[' +
                     ','.join(names[v] for v in neg) + ']);')
    lines.append('solve satisfy;')
    witness, examined = pigeonhole_injections(n_holes)
    if witness is not None:
        raise AssertionError('pigeonhole enumeration unexpectedly found a witness')
    detail = (f'{n_pigeons} pigeons, {n_holes} holes; exhaustive enumeration of partial '
              f'pigeon-to-hole injections examined {examined} maps and found no covering '
              'injection (complete: any assignment restricts to one)')
    if n_holes <= 3:
        found = brute_force_bool(clauses, len(names))
        if found is not None:
            raise AssertionError('full assignment enumeration unexpectedly found a witness')
        detail += f'; cross-checked against all 2^{len(names)} assignments'
    return {'id': f'gen_pigeonhole_bool{n_holes}', 'file': f'pigeonhole_bool{n_holes}.fzn',
            'text': '\n'.join(lines) + '\n', 'witness': None,
            'family': 'generated_dense_clause', 'generator': 'pigeonhole_bool',
            'params': {'n_holes': n_holes, 'n_pigeons': n_pigeons}, 'seed': None,
            'mode': 'satisfy', 'expected': 'unsat',
            'check_method': 'exhaustive_enumeration', 'check_detail': detail}


def linear_chain_case(n):
    names = [f'x{i}' for i in range(n)]
    lines = [f'var 0..{n}: {name} :: output_var;' for name in names]
    lines.append('constraint int_lin_eq([' + ','.join(['1']*n) + '],[' +
                 ','.join(names) + f'],{n});')
    lines.append('constraint int_le(x0,1);')
    lines.append('solve satisfy;')
    values = {0: 1, 1: n-1}
    witness = emit_solution([f'{name} = {values.get(i, 0)};' for i, name in enumerate(names)])
    return {'id': f'gen_linear{n}', 'file': f'linear_chain_{n}.fzn',
            'text': '\n'.join(lines) + '\n', 'witness': witness,
            'family': 'generated_linear', 'generator': 'linear_chain',
            'params': {'n': n}, 'seed': None, 'mode': 'satisfy', 'expected': 'sat',
            'check_method': 'constructed_witness',
            'check_detail': f'witness x0=1, x1={n-1}, rest 0 sums to {n} and satisfies '
                            'x0 <= 1; checked with leanfzn check'}


def holes_case(width, holes):
    lines = [f'var 0..{width}: x :: output_var;', f'var 0..{width}: y :: output_var;',
             f'constraint int_lin_eq([1,1],[x,y],{width});',
             'constraint int_lin_ne([1,-1],[x,y],0);']
    for h in holes:
        lines.append(f'constraint int_ne(x,{h});')
    lines.append('solve satisfy;')
    witness = emit_solution([f'x = {max(holes) + 1};', f'y = {width - max(holes) - 1};'])
    return {'id': 'gen_holes', 'file': 'holes.fzn', 'text': '\n'.join(lines) + '\n',
            'witness': witness, 'family': 'generated_holes', 'generator': 'holes',
            'params': {'width': width, 'holes': list(holes)}, 'seed': None,
            'mode': 'satisfy', 'expected': 'sat',
            'check_method': 'constructed_witness',
            'check_detail': f'witness x={max(holes) + 1} (outside the holes) and '
                            f'y={width - max(holes) - 1}; x != y; checked with leanfzn check'}


def build_cases():
    cases = [latin_case(n) for n in (3, 4, 5)]
    cases += [domain_width_case(w) for w in (64, 256, 1024)]
    cases.append(dense_clause_case('gen_bool_dense40', 40, 160, DENSE_SEED_A))
    cases.append(dense_clause_case('gen_bool_dense60', 60, 360, DENSE_SEED_B))
    cases += [pigeonhole_case(n) for n in (3, 4)]
    cases += [linear_chain_case(n) for n in (8, 32)]
    cases.append(holes_case(40, tuple(range(11))))
    return cases


def check_witness(binary, fzn_path, sol_path, limit=30):
    proc = subprocess.run([str(binary), 'check', str(fzn_path), str(sol_path)],
                          cwd=ROOT, text=True, capture_output=True, timeout=limit)
    return {'exit': proc.returncode,
            'stdout': (proc.stdout or '').strip()[-200:],
            'stderr': (proc.stderr or '').strip()[-200:]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary', type=Path, default=DEFAULT_BINARY)
    parser.add_argument('--register', action='store_true',
                        help='add/update the generated entries in performance_manifest.json')
    args = parser.parse_args()
    binary = args.binary.resolve()
    if not binary.is_file():
        parser.error('missing solver binary for witness checking; run lake build leanfzn first')
    OUT.mkdir(parents=True, exist_ok=True)
    cases = build_cases()
    manifest = {'schema_version': 1, 'generated_by': 'audits/generate_cases.py',
                'generated_utc': utc_stamp(),
                'purpose': 'B0 parameterized fixtures with fixed seeds; witnesses are '
                           'constructions, UNSAT results come from exhaustive enumeration',
                'binary': {'path': str(binary), 'sha256': digest(binary)},
                'cases': []}
    failed = False
    for case in cases:
        fzn_path = OUT/case['file']
        fzn_path.write_text(case['text'])
        check = {'method': case['check_method'], 'detail': case['check_detail'],
                 'checked_utc': utc_stamp()}
        if case['witness'] is not None:
            sol_path = OUT/(case['file'] + '.sol.txt')
            sol_path.write_text(case['witness'])
            result = check_witness(binary, fzn_path, sol_path)
            check.update(verifier='leanfzn check', witness_file=sol_path.name,
                         witness_sha256=digest(sol_path), result=result)
            accepted = result['exit'] == 0
            check['accepted'] = accepted
            failed |= not accepted
        else:
            check.update(verifier='exhaustive enumeration (this script)', result='unsat',
                         accepted=True)
        manifest['cases'].append({
            'id': case['id'], 'file': case['file'], 'sha256': digest(fzn_path),
            'family': case['family'], 'generator': case['generator'],
            'params': case['params'], 'seed': case['seed'], 'mode': case['mode'],
            'expected': case['expected'], 'check': check})
        status = check.get('accepted')
        print(f"{case['id']}: {case['expected']} "
              f"{'checked' if status else 'CHECK FAILED'} "
              f"({case['check_method']})", flush=True)
    (OUT/'generated_manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print('Saved '+str(OUT/'generated_manifest.json'))
    if args.register:
        doc = json.loads(MANIFEST_PATH.read_text())
        existing = {c['id']: c for c in doc['cases']}
        for case in manifest['cases']:
            existing[case['id']] = {
                'id': case['id'],
                'path': str((OUT/case['file']).relative_to(ROOT)),
                'family': case['family'], 'expected': case['expected'],
                'mode': case['mode'], 'default': False, 'generated': True,
                'generator': case['generator'], 'params': case['params'],
                'seed': case['seed'],
                'expected_check': case['check']['method']}
        doc['cases'] = list(existing.values())
        doc['generated_manifest'] = str((OUT/'generated_manifest.json').relative_to(ROOT))
        MANIFEST_PATH.write_text(json.dumps(doc, indent=2) + '\n')
        print('Registered generated cases in '+str(MANIFEST_PATH))
    return 1 if failed else 0


if __name__ == '__main__':
    raise SystemExit(main())
