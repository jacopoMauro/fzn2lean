#!/usr/bin/env python3
"""Short, budgeted public FlatZinc runs. Build leanfzn explicitly before use.

Per case the runner records wall time, verdict classification, raw stdout/stderr
paths, peak RSS, streamed solution timestamps (time to first solution, time to
optimum) and the parsed objective trajectory. `--source-snapshot` copies the
measured Lean sources and writes a path+sha256 manifest plus the
`lake env lean --version` output into the run directory. The runner never
builds; every child
process is killed as a process group at its external wall limit, which is capped
at 300 seconds, and the suite budget still bounds the whole run.
"""
from __future__ import annotations
import argparse
import datetime
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import re
import resource
import select
import shutil
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
TIERS = {'quick': 2, 'short': 10, 'medium': 60, 'long': 300}
MAX_PROCESS_S = 300
SEPARATOR = '----------'
UNSAT_MARKER = '=====UNSATISFIABLE====='
OPTIMUM_MARKER = '=========='
DEFAULT_POLL_S = 0.02
OBJECTIVE_RE = re.compile(r'\bsolve\b[^;]*?\b(?:maximize|minimize)\s+([A-Za-z_][A-Za-z0-9_]*)')


def classify_outcome(rc, timed_out, nsol, unsat, optimum):
    """Unknown/incomplete is distinct from a false terminal claim or error."""
    if timed_out:
        return 'timeout_with_incumbent' if nsol else 'timeout'
    if unsat and (rc != 1 or nsol or optimum):
        return 'error'
    if optimum and (rc != 0 or not nsol):
        return 'error'
    if rc == 4:
        return 'incomplete_with_incumbent' if nsol else 'unknown'
    if rc == 1 and unsat:
        return 'unsat'
    if rc == 0 and nsol:
        return 'sat'
    return 'unsupported' if rc == 3 else 'error'


def permitted_incomplete(case, row):
    """Explicit migration allowance, without changing the mathematical expectation."""
    return (case.get('allow_incomplete', False) and
            row['outcome'] in ('unknown', 'incomplete_with_incumbent') and
            (case['expected'] != 'unsat' or row['solutions'] == 0))


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def vmhwm_kib(pid):
    """Peak resident set size (KiB) of a live process from /proc/<pid>/status."""
    try:
        with open(f'/proc/{pid}/status', 'r', encoding='ascii', errors='replace') as f:
            for line in f:
                if line.startswith('VmHWM:'):
                    return int(line.split()[1])
    except (OSError, ValueError, IndexError):
        return None
    return None


def objective_value(block, objective_var):
    """The objective variable's value in one emitted solution block, if parseable."""
    if not objective_var:
        return None
    match = re.search(r'(?m)^\s*' + re.escape(objective_var) + r'\s*=\s*(-?\d+)\s*;', block)
    return int(match.group(1)) if match else None


def run(argv, limit, stdout, stderr, objective_var=None, poll_s=DEFAULT_POLL_S):
    """Run one child and measure it (startup and output included).

    Peak RSS: maximum /proc/<pid>/status VmHWM sample while the child lives.
    If the child exits before the first sample, the RUSAGE_CHILDREN ru_maxrss
    high-water mark is used: exact when the mark grew during this child,
    otherwise an upper bound inherited from earlier children.

    Solution timestamps are stdout-observation times, i.e. upper bounds on the
    solver's emission time with the poll interval as slack (the solver flushes
    after every improving solution).
    """
    if not math.isfinite(limit) or not 0 < limit <= MAX_PROCESS_S:
        raise ValueError('child limit must be positive and at most 300 seconds')
    if not math.isfinite(poll_s) or not 0 < poll_s <= 1:
        raise ValueError('poll interval must be positive and at most 1 second')
    before = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    start = time.monotonic()
    stream = []
    markers = {'unsat_s': None, 'optimum_s': None}
    peak_rss_kib = None
    peak_rss_source = 'unavailable'
    first_output_s = None
    buf = b''
    sep_bytes = SEPARATOR.encode()
    scanned = 0
    offset = 0
    with stdout.open('wb') as out, stderr.open('wb') as err:
        p = subprocess.Popen(argv, cwd=ROOT, stdout=out, stderr=err,
                             start_new_session=True)
        pidfd = None
        if hasattr(os, 'pidfd_open'):
            try:
                pidfd = os.pidfd_open(p.pid)
            except OSError:
                pidfd = None

        def pump():
            nonlocal buf, scanned, offset, first_output_s
            try:
                size = stdout.stat().st_size
            except OSError:
                return
            if size > offset:
                # Binary reads with tell(): the writer may append between a
                # size check and the read, and a text-mode seek could then
                # re-read already-consumed bytes.
                with stdout.open('rb') as f:
                    f.seek(offset)
                    buf += f.read()
                    offset = f.tell()
                if first_output_s is None:
                    first_output_s = time.monotonic() - start
            while True:
                index = buf.find(sep_bytes, scanned)
                if index < 0:
                    break
                block = buf[scanned:index].decode('utf-8', 'replace')
                scanned = index + len(sep_bytes)
                stream.append({'index': len(stream),
                               't_s': time.monotonic() - start,
                               'objective': objective_value(block, objective_var)})
            if markers['unsat_s'] is None and UNSAT_MARKER.encode() in buf:
                markers['unsat_s'] = time.monotonic() - start
            if markers['optimum_s'] is None and OPTIMUM_MARKER.encode() in buf:
                markers['optimum_s'] = time.monotonic() - start

        def sample():
            nonlocal peak_rss_kib, peak_rss_source
            value = vmhwm_kib(p.pid)
            if value is not None and (peak_rss_kib is None or value > peak_rss_kib):
                peak_rss_kib = value
                peak_rss_source = 'proc_vmhwm'

        timed_out = False
        try:
            while True:
                remaining = limit - (time.monotonic() - start)
                if remaining <= 0:
                    timed_out = True
                    break
                if pidfd is not None:
                    ready, _, _ = select.select([pidfd], [], [], min(poll_s, remaining))
                else:
                    ready = p.poll() is not None
                    if not ready:
                        time.sleep(min(poll_s, remaining))
                pump()
                sample()
                if ready:
                    break
        finally:
            if pidfd is not None:
                os.close(pidfd)
        if timed_out:
            try:
                os.killpg(p.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        p.wait()
        pump()
    wall_s = time.monotonic() - start
    after = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    if peak_rss_kib is None and after > 0:
        peak_rss_kib = after
        peak_rss_source = ('rusage_children_exact' if after > before
                           else 'rusage_children_upper_bound')
    return {'argv': argv, 'limit_s': limit, 'wall_s': wall_s,
            'exit': p.returncode, 'timeout': timed_out,
            'stdout': str(stdout), 'stderr': str(stderr),
            'peak_rss_kib': peak_rss_kib, 'peak_rss_source': peak_rss_source,
            'ru_maxrss_children_kib': after,
            'first_output_s': first_output_s,
            'time_to_first_solution_s': stream[0]['t_s'] if stream else None,
            'time_to_last_solution_s': stream[-1]['t_s'] if stream else None,
            'unsat_marker_s': markers['unsat_s'],
            'optimum_marker_s': markers['optimum_s'],
            'solutions_stream': stream}


def write_source_snapshot(output, binary):
    """Copy the measured source tree, hash it, and probe the Lean version."""
    def git(*cmd):
        try:
            return subprocess.check_output(['git', *cmd], cwd=ROOT, text=True,
                                           stderr=subprocess.DEVNULL).strip()
        except (OSError, subprocess.CalledProcessError):
            return None

    sources = sorted(ROOT.glob('LeanFzn/**/*.lean'))
    sources += [ROOT/name for name in ('lakefile.toml', 'lean-toolchain', 'lake-manifest.json')]
    snapshot_root = output/'source_snapshot_files'
    files = []
    for path in sources:
        if not path.is_file():
            continue
        relative = path.relative_to(ROOT)
        files.append({'path': str(relative), 'sha256': digest(path),
                      'size': path.stat().st_size})
        target = snapshot_root/relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(path, target)
    lean_version = None
    lean_version_error = None
    # Bounded and file-backed: a pipe-based capture can hang when lake has
    # spawned descendants or waits on another build's lock.
    probe = run(['lake', 'env', 'lean', '--version'], 30,
                output/'lean_version.stdout', output/'lean_version.stderr')
    if probe['timeout']:
        lean_version_error = 'lake env lean --version timed out after 30s'
    elif probe['exit'] == 0:
        lean_version = Path(probe['stdout']).read_text(errors='replace').strip()
    else:
        lean_version_error = (Path(probe['stderr']).read_text(errors='replace').strip()
                              or f"exit {probe['exit']}")
    snapshot = {
        'schema_version': 1,
        'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'purpose': 'copies plus a path+sha256 manifest of the measured Lean '
                   'sources; git_head/git_status locate the baseline (a full '
                   'git diff is skipped because it can take minutes here)',
        'git_head': git('rev-parse', 'HEAD'),
        'git_status': git('status', '--porcelain'),
        'lean_version': lean_version,
        'lean_version_error': lean_version_error,
        'lean_version_probe': {k: probe[k] for k in
                               ('argv', 'limit_s', 'wall_s', 'exit', 'timeout',
                                'stdout', 'stderr')},
        'binary': {'path': str(binary), 'sha256': digest(binary)},
        'file_count': len(files),
        'total_bytes': sum(f['size'] for f in files),
        'files': files}
    (output/'source_snapshot.json').write_text(json.dumps(snapshot, indent=2) + '\n')
    return snapshot


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=Path, default=ROOT/'audits/performance_manifest.json')
    parser.add_argument('--binary', type=Path, default=ROOT/'.lake/build/bin/leanfzn')
    parser.add_argument('--tier', choices=TIERS, default='quick')
    parser.add_argument('--case', action='append', default=[])
    parser.add_argument('--suite-budget', type=float)
    parser.add_argument('--repetitions', type=int, default=1)
    parser.add_argument('--poll-interval', type=float, default=DEFAULT_POLL_S,
                        help='stdout/RSS polling period in seconds (default 0.02)')
    parser.add_argument('--source-snapshot', action='store_true',
                        help='write source_snapshot.json for the measured tree')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.repetitions < 1:
        parser.error('repetitions must be positive')
    if not math.isfinite(args.poll_interval) or not 0 < args.poll_interval <= 1:
        parser.error('poll interval must be finite, positive and at most 1 second')
    budget = 60 if args.suite_budget is None else args.suite_budget
    if not math.isfinite(budget) or budget <= 0:
        parser.error('suite budget must be finite and positive')
    if args.tier in ('medium', 'long') and (not args.case or args.suite_budget is None):
        parser.error('medium/long require explicit --case selection and --suite-budget')
    binary = args.binary.resolve()
    if not binary.is_file():
        parser.error('missing solver binary; run lake build leanfzn first')
    manifest = json.loads(args.manifest.read_text())
    cases = manifest['cases']
    known = {c['id'] for c in cases}
    if set(args.case)-known:
        parser.error('unknown cases: '+', '.join(sorted(set(args.case)-known)))
    selected = [c for c in cases if c['id'] in args.case] if args.case else [c for c in cases if c['default']]
    for case in selected:
        if not (ROOT/case['path']).is_file():
            parser.error('missing input: '+case['path'])
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
    output = (args.output or ROOT/'tmp/performance'/stamp).resolve()
    output.mkdir(parents=True, exist_ok=True)
    if (output/'results.json').exists():
        parser.error('output already has results.json; choose a fresh directory')
    def git(*cmd):
        return subprocess.check_output(['git', *cmd], cwd=ROOT, text=True)
    result = {'schema_version': 1, 'timestamp_utc': stamp, 'tier': args.tier,
              'suite_budget_s': budget, 'per_solver_cap_s': TIERS[args.tier],
              'poll_interval_s': args.poll_interval, 'repetitions': args.repetitions,
              'selected_cases': [case['id'] for case in selected],
              'binary': str(binary), 'binary_sha256': digest(binary),
              'manifest_sha256': digest(args.manifest), 'git_head': git('rev-parse','HEAD').strip(),
              'git_status': git('status','--porcelain'), 'host': platform.platform(),
              'cpu_count': os.cpu_count(), 'source_snapshot': None, 'cases': [],
              'skipped': [], 'summary': {},
              'limitations': ['No internal Core phase counters; Legacy timing tools do not measure the public Core path.',
                              'Solution timestamps are stdout-observation times bounded by the poll interval.',
                              'Peak RSS prefers polled /proc VmHWM; the RUSAGE_CHILDREN fallback can be an upper bound.',
                              'Witness checking does not independently establish optimality or UNSAT.',
                              'Generated cases are deterministic but a cohort must still be frozen before comparing versions.']}
    def save():
        rows = result['cases']
        outcomes = {}
        for row in rows:
            outcomes[row['outcome']] = outcomes.get(row['outcome'], 0) + 1
        checked = [row for row in rows if 'witnesses_accepted' in row]
        result['summary'] = {
            'cases_run': len(rows),
            'outcomes': outcomes,
            'complete': sum(1 for row in rows if row.get('complete')),
            'expected_agreement': sum(1 for row in rows if row.get('expected_agrees')),
            'contract_agreement': sum(1 for row in rows if row.get('contract_agrees')),
            'allowed_incomplete': sum(1 for row in rows if row.get('permitted_incomplete')),
            'witness_checks': len(checked),
            'witnesses_accepted': sum(1 for row in checked if row['witnesses_accepted']),
            'total_solve_wall_s': round(sum(row['solve']['wall_s'] for row in rows), 6),
            'max_peak_rss_kib': max((row['peak_rss_kib'] or 0 for row in rows), default=None),
            'skipped': len(result['skipped'])}
        tmp = output/'results.json.tmp'
        tmp.write_text(json.dumps(result, indent=2)+'\n')
        tmp.replace(output/'results.json')
    start = time.monotonic()
    failed = False
    save()
    if args.source_snapshot:
        write_source_snapshot(output, binary)
        result['source_snapshot'] = str(output/'source_snapshot.json')
        save()
    for rep in range(args.repetitions):
        for case in selected:
            remaining = budget-(time.monotonic()-start)
            label = f"{case['id']}.{rep}"
            if remaining <= 0:
                result['skipped'].append({'id': case['id'], 'rep': rep, 'reason': 'suite_budget'})
                save()
                continue
            path = ROOT/case['path']
            objective_var = None
            if case.get('mode') != 'satisfy':
                match = OBJECTIVE_RE.search(path.read_text(errors='replace'))
                objective_var = match.group(1) if match else None
            row = {'id':case['id'], 'rep':rep, 'family':case['family'],
                   'expected':case['expected'], 'input_sha256':digest(path),
                   'objective_var':objective_var}
            row['solve'] = run([str(binary),'solve',str(path)], min(TIERS[args.tier], remaining),
                               output/(label+'.stdout'), output/(label+'.stderr'),
                               objective_var=objective_var, poll_s=args.poll_interval)
            text = Path(row['solve']['stdout']).read_text(errors='replace')
            lines = text.splitlines()
            nsol = lines.count('----------')
            rc = row['solve']['exit']
            timeout = row['solve']['timeout']
            unsat = '=====UNSATISFIABLE=====' in lines
            optimum = '==========' in lines
            row.update(solutions=nsol, optimum_marker=optimum,
                       peak_rss_kib=row['solve']['peak_rss_kib'],
                       peak_rss_source=row['solve']['peak_rss_source'],
                       time_to_first_solution_s=row['solve']['time_to_first_solution_s'],
                       time_to_last_solution_s=row['solve']['time_to_last_solution_s'],
                       time_to_optimum_s=row['solve']['optimum_marker_s'],
                       objective_trajectory=row['solve']['solutions_stream'],
                       complete=not timeout and ((rc == 1 and unsat) or
                           (rc == 0 and nsol > 0 and (case['mode']=='satisfy' or optimum))))
            row['outcome'] = classify_outcome(rc, timeout, nsol, unsat, optimum)
            row['allow_incomplete'] = case.get('allow_incomplete', False)
            row['permitted_incomplete'] = permitted_incomplete(case, row)
            row['expected_agrees'] = (case['expected']=='unknown' or
                row['outcome'] in ('timeout','timeout_with_incumbent') or
                case['expected']==row['outcome'])
            row['contract_agrees'] = row['expected_agrees'] or row['permitted_incomplete']
            # Check complete emitted solutions only: ignore an interrupted final store.
            remaining = budget-(time.monotonic()-start)
            if nsol and remaining > 0:
                solutions = text.rsplit('----------', 1)[0]+'----------\n'
                solpath = output/(label+'.solutions')
                solpath.write_text(solutions)
                row['check'] = run([str(binary),'check',str(path),str(solpath)],
                                   min(10,remaining), output/(label+'.check.stdout'),
                                   output/(label+'.check.stderr'),
                                   poll_s=args.poll_interval)
                row['witnesses_accepted'] = not row['check']['timeout'] and row['check']['exit']==0
            elif nsol:
                row['witnesses_accepted'] = None
                row['check_skipped'] = 'suite_budget'
            failed |= (not row['contract_agrees'] or row['outcome']=='error' or
                       row.get('witnesses_accepted') is False)
            result['cases'].append(row)
            result['elapsed_s'] = time.monotonic()-start
            save()
            first = row['time_to_first_solution_s']
            print(f"{label}: {row['outcome']} {row['solve']['wall_s']:.3f}s "
                  f"solutions={nsol} complete={row['complete']} "
                  f"rss={row['peak_rss_kib']}KiB "
                  f"first_sol={first if first is None else format(first, '.3f')}", flush=True)
    print('Saved '+str(output/'results.json'))
    return 1 if failed else 0


if __name__ == '__main__':
    raise SystemExit(main())
