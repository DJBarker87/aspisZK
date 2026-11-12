#!/usr/bin/env python3
"""X2b: list the Lean errors of one native compile by enclosing declaration of the raw Funs.lean.
Usage: fv_x2b_errs.py <native dir> (reads exit.txt, Funs.log, src/<ns>/Funs.lean). Output: per declaration, the error
count and the first two messages (line, first line of the message); then totals per module."""
import re, sys
from pathlib import Path
D = Path(sys.argv[1])
decl = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:noncomputable |partial |private |divergent )*(?:def|theorem|abbrev|instance|structure|impl_def|axiom|opaque)\s+(\S+)')
print('exit:', ' '.join((D / 'exit.txt').read_text().split()) if (D / 'exit.txt').exists() else 'none')
for M in ('TypesExternal', 'Types', 'FunsExternal', 'Funs'):
    lg = D / (M + '.log')
    if not lg.exists(): continue
    log = lg.read_text(errors='replace')
    src = next(D.glob('src/*/%s.lean' % M), None)
    lines = src.read_text(errors='replace').split('\n') if src else []
    starts = [(i + 1, decl.match(l).group(1)) for i, l in enumerate(lines) if decl.match(l)]
    def enc(n):
        b = None
        for i, nm in starts:
            if i <= n: b = nm
            else: break
        return b
    per = {}
    for m in re.finditer(r'^\S*?%s\.lean:(\d+):(\d+): error(?:\([^)]*\))?: (.*)$' % M, log, re.M):
        ln = int(m.group(1)); per.setdefault(enc(ln), []).append((ln, m.group(3)[:200]))
    tot = sum(len(v) for v in per.values())
    print('== %s: %d errors in %d declarations' % (M, tot, len(per)))
    for k, v in per.items():
        print('%3d %s' % (len(v), k))
        for ln, msg in v[:2]: print('      %d %s' % (ln, msg))
