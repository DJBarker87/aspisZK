#!/usr/bin/env python3
"""X1b gate (fault 1): the Aspis (or probe) functions whose LLBC body calls both a reversing adapter
(`Iterator::rev` or a method of `core::iter::adapters::rev`) and a mutable slice iterator (`iter_mut`,
`chunks_mut`, `chunks_exact_mut`, or a method of `IterMut` / `ChunksMut` / `ChunksExactMut`). The privacy lead's
mutiter_calls.py has the same families but reads the LLBC through c2_graph.py, which stops on this Charon's format;
this is the same family rule over fv_x1b_llbc.py.
usage: fv_x1b_mutiter.py <out.llbc> <crate prefix>...   (prints TSV: function, file, line, rev callees, mut callees)"""
import re, sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from fv_x1b_llbc import LLBC
g = LLBC(sys.argv[1]); pre = tuple(sys.argv[2:]) or ('aspis_',)
REV = re.compile(r'Iterator::rev$|adapters::rev::'); MUT = re.compile(r'::iter_mut$|chunks_mut$|chunks_exact_mut$|IterMut|ChunksMut|ChunksExactMut|slice::iter::\{impl\}::next$')
print('function\tfile\tline\trev callees\tmutable-iterator callees')
n = 0
for i, fs in g.direct.items():
    if not g.name[i].startswith(pre): continue
    names = {g.name.get(c, '') for c in fs}
    r = sorted(x for x in names if REV.search(x)); m = sorted(x for x in names if MUT.search(x) and ('mut' in x.lower() or 'Mut' in x))
    if r and m:
        f, l = g.span(i); print('%s\t%s\t%s\t%s\t%s' % (g.name[i], f, l, ' '.join(r), ' '.join(m))); n += 1
print('# functions with both %d' % n, file=sys.stderr)
