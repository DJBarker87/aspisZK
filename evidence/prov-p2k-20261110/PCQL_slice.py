#!/usr/bin/env python3
"""PCQL_slice.py FUNS.lean ROOT[,ROOT...] : print the declaration blocks of an Aeneas Funs file that the roots depend on (transitive, by identifier occurrence)."""
import sys,re
src=open(sys.argv[1]).read();roots=sys.argv[2].split(',')
parts=re.split(r'(?m)^(?=/-- \[)',src);head=parts[0];blocks=parts[1:]
def name(b):
    m=re.search(r'(?m)^(?:@\[[^\n]*\]\s*)*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:def|abbrev|theorem|structure|inductive)\s+(\S+)',b)
    return m.group(1) if m else None
names=[name(b) for b in blocks]
idx={n:i for i,n in enumerate(names) if n}
need=set();todo=[idx[r] for r in roots]
while todo:
    i=todo.pop()
    if i in need:continue
    need.add(i)
    body=blocks[i].split('\n',3)[-1] if False else blocks[i]
    body=re.sub(r'(?s)^/--.*?-/','',body,count=1)
    for n,j in idx.items():
        if j!=i and j not in need and re.search(r'(?<![\w.])'+re.escape(n)+r'(?![\w])',body):todo.append(j)
out=''.join(blocks[i] for i in sorted(need))
sys.stdout.write(out)
sys.stderr.write('kept %s\n'%[names[i] for i in sorted(need)])
