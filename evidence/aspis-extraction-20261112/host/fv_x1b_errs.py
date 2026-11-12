#!/usr/bin/env python3
"""X1b: one row per Lean error of a native probe's Funs.log: line, enclosing declaration (the last doc-commented block
starting at or before the line), its Rust source path and span, and the first line of the message.
usage: fv_x1b_errs.py <probe dir>   (reads <dir>/Funs.log and <dir>/src/AspisX1/Funs.lean; prints TSV)"""
import re, sys
from pathlib import Path
D = Path(sys.argv[1]); src = (D / 'src/AspisX1/Funs.lean').read_text().split('\n')
starts = []  # (line, decl name, source)
doc = None
for i, l in enumerate(src, 1):
    if l.startswith('/-- '): doc = i
    m = re.match(r'^(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+|partial\s+)*(def|axiom|opaque|structure|inductive|instance|theorem)\s+(\S+)', l)
    if m:
        s = ''
        if doc:
            for k in range(doc - 1, i):
                mm = re.search(r"Source: '([^']*)', lines (\S+)", src[k])
                if mm: s = '%s %s' % (mm.group(1), mm.group(2))
        starts.append((doc or i, m.group(2), s)); doc = None
print('line\tdeclaration\tsource\tmessage')
for l in (D / 'Funs.log').read_text(errors='replace').split('\n'):
    m = re.match(r'.*Funs\.lean:(\d+):(\d+): error[^:]*: ?(.*)', l)
    if not m: continue
    n = int(m.group(1)); dec = max((s for s in starts if s[0] <= n), default=(0, '?', ''))
    print('%d\t%s\t%s\t%s' % (n, dec[1], dec[2], m.group(3)[:160]))
