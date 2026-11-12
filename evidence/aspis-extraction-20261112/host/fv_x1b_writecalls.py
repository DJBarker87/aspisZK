#!/usr/bin/env python3
"""X1b gate (account write route): every call, from an Aspis function body of one LLBC, of a function whose name is
one of the mutable account handles: `try_borrow_mut_data`, `try_borrow_mut_lamports`, `RefCell` `borrow_mut` /
`try_borrow_mut`, or `deref_mut` / `index_mut` of `core::cell::RefMut` (an impl in `core::cell`). Edge rule: a
`Fun Regular` pointer in the body outside Drop (fv_x1b_llbc.py). Pass condition: the callers are only the account
write-boundary functions. A function inlined into its caller by optimized dependency MIR shows under the caller.
usage: fv_x1b_writecalls.py <out.llbc>   (prints TSV: caller, file, line, callee; '# names' lists every matching
callee name present in the LLBC, called or not)"""
import re, sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from fv_x1b_llbc import LLBC
PAT = re.compile(r'try_borrow_mut_data$|try_borrow_mut_lamports$|^core::cell::.*(try_)?borrow_mut$|^core::cell::\{impl\}::deref_mut$|^core::cell::\{impl\}::index_mut$')
g = LLBC(sys.argv[1])
print('caller\tfile\tline\tcallee')
n = 0
for i, funs in sorted(g.direct.items(), key=lambda kv: g.name[kv[0]]):
    if not g.name[i].startswith('aspis_'): continue
    for c in sorted(funs, key=lambda c: g.name.get(c, '')):
        cn = g.name.get(c, '')
        if PAT.search(cn):
            f, l = g.span(i); print('%s\t%s\t%s\t%s' % (g.name[i], f, l, cn)); n += 1
print('# names ' + ' | '.join(sorted({v for v in g.name.values() if PAT.search(v)})))
print('# calls %d' % n, file=sys.stderr)
