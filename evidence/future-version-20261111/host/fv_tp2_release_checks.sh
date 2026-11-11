#!/bin/bash
# Translatability pass, statement worker (T2): release-style checks of one emission. Reads only.
# usage: fv_tp2_release_checks.sh <charon-run> <aeneas-run> <namespace>
#  1 completeness: every structured aspis_statement function of Charon's declaration list has a
#    definition in the emitted Funs.lean (matched by the Rust name in Aeneas's doc comment);
#  2 erased-region scan: every mutable reference type in the LLBC whose region is erased, with the
#    declaration it occurs in (the shape behind the dropped-write defect of iter_mut().rev()).
exec python3 - "$@" <<'PY'
import json, re, sys
from pathlib import Path
E = Path('/home/dombarker/project-offloads/future-version-20261111/tp2/runs')
crun, arun, ns = sys.argv[1:4]
decls = json.load(open(E / crun / 'declarations.json'))
funs = (E / arun / 'raw' / ns / 'Funs.lean').read_text()
ext = (E / arun / 'raw' / ns / 'FunsExternal_Template.lean').read_text() if (E / arun / 'raw' / ns / 'FunsExternal_Template.lean').exists() else ''
DOC = re.compile(r'(?m)^/-- (?!Trait implementation)\[(.*)\](?::[^\]]*)?$')
doc = DOC.findall(funs) + DOC.findall(ext)
def strip_braces(n):
    out, depth = [], 0
    for ch in n:
        if ch == '{': depth += 1; continue
        if ch == '}': depth -= 1; continue
        if depth == 0: out.append(ch)
    t = re.sub(r'<[^<>]*>', '', ''.join(out))
    while '<' in t: t = re.sub(r'<[^<>]*>', '', t)
    return re.sub(r'(::)+', '::', ' '.join(t.split()))
from collections import Counter
emitted = Counter(strip_braces(d) for d in doc)
local = [d for d in decls if d['name'].startswith(('aspis_statement', 'aspis_core')) and d['body'] == 'Structured']
want = Counter(strip_braces(d['name']) for d in local)
missing = {k: v - emitted.get(k, 0) for k, v in want.items() if v > emitted.get(k, 0)}
print('charon structured aspis_statement and aspis_core declarations:', len(local), ' emitted doc-named definitions (Funs + FunsExternal):', len(doc))
print('missing from the emission (normalised name, count):', sum(missing.values()))
for k, v in sorted(missing.items()): print('   %d  %s' % (v, k))
doc_llbc = json.load(open(E / crun / 'out.llbc'))
tr = doc_llbc.get('translated', doc_llbc)
hits = []
local_refs = []
def walk(x, where, targ=False):
    if isinstance(x, dict):
        if 'Ref' in x and isinstance(x['Ref'], list) and len(x['Ref']) == 3:
            r, t, k = x['Ref']
            if k == 'Mut' and (r == 'Erased' or (isinstance(r, dict) and 'Erased' in r)):
                (hits if targ else local_refs).append(where)
        for key, v in x.items(): walk(v, where, targ or key == 'generics')
    elif isinstance(x, list):
        for v in x: walk(v, where, targ)
def name(meta):
    out = []
    for p in meta['name']:
        out.append(p['Ident'][0] if 'Ident' in p else '{impl}')
    return '::'.join(out)
for f in tr.get('fun_decls', []):
    if f is None: continue
    walk(f, name(f['item_meta']))
from collections import Counter
c = Counter(hits)
print('mutable references with an erased region as local or operand types (ordinary in LLBC bodies):', len(local_refs))
print('mutable-borrow TYPE ARGUMENTS (inside generics) with an erased region:', sum(c.values()), 'in', len(c), 'declarations')
for k, v in sorted(c.items()): print('   %4d  %s' % (v, k))
PY
