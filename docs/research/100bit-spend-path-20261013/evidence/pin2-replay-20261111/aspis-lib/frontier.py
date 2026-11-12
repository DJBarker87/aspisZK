#!/usr/bin/env python3
"""Carrier-free import frontier: imports of <module> with every carrier (kind-d) import replaced,
recursively, by that carrier's own imports. Prints the resulting non-carrier import list."""
import sys,os,re
src,dfile=sys.argv[1],sys.argv[2]; mods=sys.argv[3:]
d=set(l.split('\t')[0].strip() for l in open(dfile) if l.strip() and not l.startswith('d_module'))
def imports(m):
    p=os.path.join(src,m.replace('.','/')+'.lean')
    if not os.path.exists(p): return []
    return [l.split()[1] for l in open(p,errors='ignore') if l.startswith('import ')]
for m in mods:
    out=[];seen=set();stack=list(reversed(imports(m)))
    while stack:
        x=stack.pop()
        if x in seen: continue
        seen.add(x)
        if x in d: stack.extend(reversed(imports(x)))
        else: out.append(x)
    print(m+'\t'+' '.join(out))
