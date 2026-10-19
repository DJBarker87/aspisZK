#!/usr/bin/env python3
"""needj.py MANIFEST OLDSRC JSRC ROOT... -- read-only: project modules (sources under OLDSRC) in ROOTs' closure
that are not in the J manifest; whether J/sources already has them; topological order."""
import sys, os, re, json
man = json.load(open(sys.argv[1])); inman = {e['module'] for e in man['order']}
old, js, roots = sys.argv[2], sys.argv[3], sys.argv[4:]
IMP = re.compile(r'^\s*import\s+([\w.]+)')
def src(base, m): return os.path.join(base, m.replace('.', '/') + '.lean')
def imps(m):
    f = src(old, m)
    return [mm.group(1) for l in open(f) for mm in [IMP.match(l)] if mm] if os.path.exists(f) else []
seen, order = set(), []
def visit(m):
    if m in seen or m in inman or not os.path.exists(src(old, m)): return
    seen.add(m)
    for x in imps(m): visit(x)
    order.append(m)
for r in roots: visit(r)
import hashlib
def sha(f): return hashlib.sha256(open(f, 'rb').read()).hexdigest() if os.path.exists(f) else None
for m in order:
    print(m, 'J-has-source' if os.path.exists(src(js, m)) else 'J-missing', sha(src(old, m))[:12], (sha(src(js, m)) or '-')[:12],
          'imports:', [x for x in imps(m) if not x.startswith('Mathlib') and not x.startswith('Aeneas')])
