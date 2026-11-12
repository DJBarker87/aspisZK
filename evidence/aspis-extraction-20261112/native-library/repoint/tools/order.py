#!/usr/bin/env python3
"""Usage: order.py <lean_dir> <root>... : chain modules (files in lean_dir) in the import closure of roots, topological order."""
import sys,os
d=sys.argv[1]; roots=sys.argv[2:]
chain={f[:-5] for f in os.listdir(d) if f.endswith('.lean')}
def imps(m):
    return [l.split()[1] for l in open(os.path.join(d,m+'.lean')) if l.startswith('import ')]
out=[];seen=set()
def visit(m):
    if m in seen: return
    seen.add(m)
    for i in imps(m):
        if i in chain: visit(i)
    out.append(m)
for r in roots: visit(r)
print('\n'.join(out))
