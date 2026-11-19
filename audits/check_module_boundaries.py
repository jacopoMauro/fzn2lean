#!/usr/bin/env python3
"""Check imports, cycles and active proof holes without requiring Lean artifacts."""
from pathlib import Path
import re
import sys
ROOT = Path(__file__).resolve().parent.parent
def code_in(source):
    """Mask nested Lean comments and strings while preserving line numbers."""
    chars = list(source)
    i = 0
    depth = 0
    quoted = False
    while i < len(source):
        if depth:
            if source.startswith('/-', i):
                chars[i:i + 2] = '  '; depth += 1; i += 2
            elif source.startswith('-/', i):
                chars[i:i + 2] = '  '; depth -= 1; i += 2
            else:
                if source[i] != '\n': chars[i] = ' '
                i += 1
        elif quoted:
            if source[i] == '\\' and i + 1 < len(source):
                chars[i] = ' '
                if source[i + 1] != '\n': chars[i + 1] = ' '
                i += 2
            else:
                if source[i] == '"': quoted = False
                if source[i] != '\n': chars[i] = ' '
                i += 1
        elif source.startswith('/-', i):
            chars[i:i + 2] = '  '; depth = 1; i += 2
        elif source.startswith('--', i):
            while i < len(source) and source[i] != '\n':
                chars[i] = ' '; i += 1
        elif source[i] == '"':
            chars[i] = ' '; quoted = True; i += 1
        else:
            i += 1
    return ''.join(chars)

def imports_in(source):
    imports = re.findall(r'^\s*import[ \t]+([^\n]+)', code_in(source), re.MULTILINE)
    return [name for line in imports for name in re.findall(r'[\w.]+', line)]

paths = (list((ROOT / 'LeanFzn').rglob('*.lean')) +
         list((ROOT / 'Tests').rglob('*.lean')) + [ROOT / 'LeanFzn.lean', ROOT / 'Main.lean'])
modules = {
    str(p.relative_to(ROOT).with_suffix('')).replace('/', '.'): imports_in(p.read_text())
    for p in paths
}
rules = {
    'Tests.Parser': ['LeanFzn.Legacy', 'Tests.Legacy'],
    'Tests.Semantics': ['LeanFzn.Legacy', 'Tests.Legacy'],
    'Tests.Checker': ['LeanFzn.Legacy', 'Tests.Legacy'],
    'Tests.Compiler': ['LeanFzn.Legacy', 'Tests.Legacy'],
    'Tests.Engine': ['LeanFzn.Legacy', 'Tests.Legacy'],
    'Tests.Integration': ['LeanFzn.Legacy', 'Tests.Legacy'],
    'LeanFzn': ['LeanFzn.Legacy'],
    'Main': ['LeanFzn.Legacy'],
    'LeanFzn.Cli': ['LeanFzn.Legacy'],
    'LeanFzn.Engine': ['LeanFzn.Legacy'],
    'LeanFzn.Integration': ['LeanFzn.Legacy'],
    'LeanFzn.Checker.Runtime': ['LeanFzn.Checker.Proofs'],
    'LeanFzn.Integration.Config.Types': ['LeanFzn.Solver', 'LeanFzn.Engine', 'LeanFzn.Checker'],
    'LeanFzn.Integration.Config.Validate': ['LeanFzn.Solver', 'LeanFzn.Engine', 'LeanFzn.Checker'],
    'LeanFzn.Integration.Config.Parse': ['LeanFzn.Solver', 'LeanFzn.Engine', 'LeanFzn.Checker'],
    'LeanFzn.Integration.Config.Annotations': ['LeanFzn.Legacy', 'LeanFzn.Engine', 'LeanFzn.Checker'],
    'LeanFzn.Engine.Queue.Types': ['LeanFzn.Engine.Proofs.Queue'],
    'LeanFzn.Engine.Queue.Worklist': ['LeanFzn.Engine.Proofs.Queue'],
    'LeanFzn.Engine.Queue.Apply': ['LeanFzn.Engine.Proofs.Queue'],
    'LeanFzn.Engine.Queue.Run': ['LeanFzn.Engine.Proofs.Queue'],
    'LeanFzn.Parser': ['LeanFzn.Solver', 'LeanFzn.Checker', 'LeanFzn.Compiler', 'LeanFzn.Integration', 'LeanFzn.Legacy'],
    'LeanFzn.Semantics': ['LeanFzn.Solver', 'LeanFzn.Checker', 'LeanFzn.Compiler', 'LeanFzn.Integration', 'LeanFzn.Legacy'],
    'LeanFzn.Checker': ['LeanFzn.Solver', 'LeanFzn.Compiler', 'LeanFzn.Integration', 'LeanFzn.Legacy'],
    'LeanFzn.Compiler': ['LeanFzn.Checker', 'LeanFzn.Integration', 'LeanFzn.Legacy'],
    'LeanFzn.Solver': ['LeanFzn.Checker', 'LeanFzn.Integration', 'LeanFzn.Legacy'],
}
errors = []
for path in paths:
    for number, line in enumerate(code_in(path.read_text()).splitlines(), 1):
        if re.search(r'\b(sorry|admit|axiom)\b', line):
            errors.append(f'{path.relative_to(ROOT)}:{number}: active proof hole or user axiom')
for root, forbidden in rules.items():
    seen = set()
    pending = [(name, [name]) for name in modules if name == root or (root != 'LeanFzn' and name.startswith(root + '.'))]
    while pending:
        name, path = pending.pop()
        if name in seen:
            continue
        seen.add(name)
        for imported in modules.get(name, []):
            if any(imported == f or imported.startswith(f + '.') for f in forbidden):
                errors.append(' -> '.join(path + [imported]))
            else:
                pending.append((imported, path + [imported]))
# The lexical specification may depend on its own pure submodules and shared
# token data, but never on the executable lexer or a downstream proof/parser.
# Check transitive imports, including dependencies hidden behind Token itself.
lexical_root = 'LeanFzn.Parser.Lexical'
def lexical_module_allowed(name):
    return name == 'LeanFzn.Parser.Token' or name == lexical_root or name.startswith(lexical_root + '.')

def is_project_module(name):
    return name in {'LeanFzn', 'Tests'} or name.startswith(('LeanFzn.', 'Tests.'))

for lexical in sorted(name for name in modules
                      if name == lexical_root or name.startswith(lexical_root + '.')):
    pending = [(lexical, [lexical])]
    seen = set()
    while pending:
        name, path = pending.pop()
        if name in seen:
            continue
        seen.add(name)
        for imported in modules.get(name, []):
            if is_project_module(imported) and not lexical_module_allowed(imported):
                errors.append('Lexical independence: ' + ' -> '.join(path + [imported]))
            else:
                pending.append((imported, path + [imported]))

# No internal component may import the optional whole-stack umbrella.
for name, imports in modules.items():
    for imported in imports:
        if imported.startswith(('LeanFzn.', 'Tests.')) and imported not in modules:
            errors.append(name + ' imports missing module ' + imported)
    if name != 'Main' and 'LeanFzn' in imports:
        errors.append(name + ' imports the whole-stack LeanFzn umbrella')
    if any(i == 'solver' or i.startswith('solver.') for i in imports):
        errors.append(name + ' retains an old solver import')
# Detect cycles independently of Lake's diagnostics.
active = set()
visited = set()
def walk(name, path):
    if name in active:
        errors.append('Import cycle: ' + ' -> '.join(path + [name]))
        return
    if name in visited:
        return
    active.add(name)
    for imported in modules.get(name, []):
        if imported in modules:
            walk(imported, path + [name])
    active.remove(name)
    visited.add(name)
for name in modules:
    walk(name, [])
for error in sorted(set(errors)):
    print(error, file=sys.stderr)
if errors:
    raise SystemExit(1)
print(f'Component boundaries passed ({len(modules)} modules; no import cycles; public Core/CLI independent of Legacy).')
