#!/usr/bin/env python3
"""X2: the overflow-check comparison. For every Rust function of the three Aspis crates with emitted Lean in either the
overflow-off (deployed) or the overflow-on run, compare the emitted text (doc block bodies under the function's name,
loop bodies and closures included, normalised as in fv_x2_compare.py) and summarise the difference by kind: checked
arithmetic (+, -, *, << and >> on machine integers become the library's checked operations) against wrapping
operations. Reads only.
usage: fv_x2_overflow.py <off Funs.lean> <on Funs.lean> <out.tsv>"""
import collections, re, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from fv_x2_compare import defs, norm   # noqa: E402  (the module runs its comparison only under __main__)
off, on, out = sys.argv[1:4]
A = {}; B = {}
for c in ('aspis_pool::', 'aspis_statement::', 'aspis_core::'):
    A.update(defs(off, c)); B.update(defs(on, c))
OPS = re.compile(r'\b(?:Std\.)?[UI](?:8|16|32|64|128|size)\.(wrapping_\w+|overflowing_\w+|checked_\w+)|\s(\+|-|\*|<<<|>>>|/|%)\s')
rows = []; n = collections.Counter()
for k in sorted(set(A) | set(B)):
    a = norm('\n'.join(A.get(k, []))); b = norm('\n'.join(B.get(k, [])))
    if k not in A or k not in B: st = 'only in the %s run' % ('on' if k not in A else 'off'); note = ''
    elif a == b: st = 'identical'; note = ''
    else:
        st = 'different'
        ca = collections.Counter(m.group(1) or m.group(2) for m in OPS.finditer(a)); cb = collections.Counter(m.group(1) or m.group(2) for m in OPS.finditer(b))
        note = 'operations off %s | on %s' % (dict(ca), dict(cb))
    n[(k.split('::')[0], st)] += 1; rows.append((k, st, note))
with open(out, 'w') as f:
    f.write('rust_path\toff_vs_on\tnote\n')
    for r in rows: f.write('\t'.join(r) + '\n')
for k, v in sorted(n.items()): print(k, v)
