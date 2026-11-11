#!/usr/bin/env python3
"""Topological order of the Aspis Lean modules in a source directory.

usage: fv_replay_order.py <srcdir> [exclude-substring ...]
Prints one module per line, every module after the modules it imports. Only imports that
resolve to a file in <srcdir> are edges; every other import is left to LEAN_PATH (R1's release
objects, Mathlib). Modules whose name contains an exclude substring are skipped and listed on
stderr, as is any module that imports a skipped one.
"""
import os, re, sys
src = sys.argv[1]
excl = sys.argv[2:]
mods = sorted(f[:-5] for f in os.listdir(src) if f.endswith('.lean'))
deps = {}
for m in mods:
    deps[m] = []
    for line in open(os.path.join(src, m + '.lean')):
        g = re.match(r'^import\s+(\S+)', line)
        if g and g.group(1) in mods:
            deps[m].append(g.group(1))
skip = {m for m in mods if any(e in m for e in excl)}
changed = True
while changed:
    changed = False
    for m in mods:
        if m not in skip and any(d in skip for d in deps[m]):
            skip.add(m); changed = True
order, seen = [], set()
def visit(m, stack=()):
    if m in seen: return
    if m in stack: raise SystemExit(f'import cycle at {m}')
    for d in deps[m]: visit(d, stack + (m,))
    seen.add(m); order.append(m)
for m in mods:
    if m not in skip: visit(m)
for m in sorted(skip): print(m, file=sys.stderr)
print('\n'.join(order))
