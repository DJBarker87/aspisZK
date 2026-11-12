#!/usr/bin/env python3
"""X7: one program's candidate emission against a reference raw emission of the same program (the worker's final
run on its own tree: X1b run G for the verifier program, X2c run c9 for the Pool). Declarations are matched by Lean
name and Aeneas label; texts are compared after dropping the doc comment and collapsing whitespace (the namespace is
the same in both). Lists every declaration that differs or occurs on one side only, with its Rust source span on
each side. Reads only.
usage: fv_emit_bodycmp.py <candidate raw dir> <reference raw dir>   (TSV on stdout; summary last)"""
import re, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from fv_emit_lean import blocks


def load(R):
    out = {}
    for f in ('Funs.lean', 'FunsExternal_Template.lean', 'Types.lean', 'TypesExternal_Template.lean'):
        for b in blocks(Path(R) / f):
            if b['kind']:
                out[(f, b['lean'], b['label'])] = (b, re.sub(r'\s+', ' ', b['text']).strip())
    return out


A, B = load(sys.argv[1]), load(sys.argv[2])
print('file\tlean_name\tlabel\tresult\tcandidate source\treference source')
cnt = {}
for k in sorted(set(A) | set(B)):
    a, b = A.get(k), B.get(k)
    if a and b and a[1] == b[1]:
        r = 'identical'
    elif a and b:
        r = 'differs'
    else:
        r = 'candidate only' if a else 'reference only'
    cnt[r] = cnt.get(r, 0) + 1
    if r != 'identical':
        s = lambda x: '%s:%s-%s' % (x[0]['file'], x[0]['a'], x[0]['b']) if x else '-'
        print('%s\t%s\t%s\t%s\t%s\t%s' % (k[0], k[1], k[2], r, s(a), s(b)))
print('# ' + ', '.join('%s %d' % kv for kv in sorted(cnt.items())))
