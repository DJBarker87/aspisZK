#!/usr/bin/env python3
"""X1b fault check (e): for every row of X1's compare-frza.tsv whose result is `different`, the unified diff of the two
emitted bodies (the per-crate freeze emission FRZE-frza, raw, against X1's whole-program emission at the freeze
scope's overflow setting: on2 for v, s, d, c; off2 for p). Bodies are the doc-commented blocks whose first doc line
names the Rust path (and the loop number for loop bodies); doc comments and attributes are dropped, the namespace
prefix is removed and runs of spaces are folded, so the diff shows only body lines. A reading aid: it says where the
two emissions differ, not which is right.
usage: fv_x1b_frzadiff.py <compare-frza.tsv> <W>   (prints the diffs)"""
import difflib, re, sys
from pathlib import Path
CMP, W = Path(sys.argv[1]), Path(sys.argv[2])
NS = dict(v='AspisTPv', p='AspisTPp', s='AspisTP2g', d='AspisTP3stmt', c='AspisTP3core')
def blocks(path, ns):
    t = path.read_text(); out = {}
    starts = [m.start() for m in re.finditer(r'^/-- ', t, flags=re.M)] + [len(t)]
    for a, b in zip(starts, starts[1:]):
        c = t[a:b]; e = c.find('-/')
        if e < 0: continue
        head = c[4:e].split('\n')[0].strip()
        head = re.sub(r'\s+', ' ', head.replace('Trait implementation: ', ''))
        body = re.sub(r'^\s*(@\[[^\]]*\]\s*)+', '', c[e + 2:].strip(), flags=re.S)
        body = body.replace(ns + '.', '').replace('_root_.', '')
        out.setdefault(head, []).append([re.sub(r' +', ' ', l.rstrip()) for l in body.split('\n') if l.strip()])
    return out
cache = {}
def get(kind, scope):
    if (kind, scope) not in cache:
        if kind == 'frza': p = W / ('frz-emit/frza/runs/A-%s-release/raw/%s/Funs.lean' % (scope, NS[scope])); ns = NS[scope]
        else: p = W / ('x1/runs/%s/runs/A-release/raw/AspisX1/Funs.lean' % ('off2' if scope == 'p' else 'on2')); ns = 'AspisX1'
        cache[(kind, scope)] = blocks(p, ns)
    return cache[(kind, scope)]
rows = [l.split('\t') for l in CMP.read_text().split('\n')[1:] if l.strip()]
n = 0
for r in rows:
    scope, fn, loop, res = r[0], r[2], r[3], r[4]
    if res != 'different': continue
    n += 1
    def find(bl):
        for h, v in bl.items():
            if h.startswith('[' + fn + ']') or h.startswith('[' + fn + ']:'):
                if (('loop' in h) == bool(loop)): return v[0]
        return None
    a, b = find(get('frza', scope)), find(get('x1', scope))
    print('=' * 100); print('%d. scope %s  %s %s  (%s)' % (n, scope, fn, '(loop body)' if loop else '', r[5][:200]))
    if a is None or b is None: print('   body not found: frza %s, X1 %s' % (a is not None, b is not None)); continue
    for l in difflib.unified_diff(a, b, 'frza', 'X1', n=1, lineterm=''): print('   ' + l)
