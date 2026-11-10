#!/usr/bin/env python3
"""NPE_: read-only probe of an existing Charon LLBC file. Finds functions whose name path
contains a given element, dumps their bodies, and lists every Shl/Shr BinaryOp node with
its operands. Usage: NPE_llbc_probe.py LLBC OUTDIR NAME..."""
import json, sys, hashlib, os
llbc, outd, names = sys.argv[1], sys.argv[2], sys.argv[3:]
raw = open(llbc, 'rb').read()
print('llbc_sha256', hashlib.sha256(raw).hexdigest())
d = json.loads(raw)
print('top keys', list(d)[:10])
tr = d.get('translated', d)
print('translated keys', list(tr)[:20])
def name_str(n):
    out = []
    for e in n:
        if isinstance(e, dict):
            if 'Ident' in e:
                v = e['Ident']; out.append(v[0] if isinstance(v, list) else str(v))
            elif 'Impl' in e: out.append('{impl}')
            else: out.append(str(list(e)[0]))
        else: out.append(str(e))
    return '::'.join(out)
funs = tr['fun_decls']
funs = funs if isinstance(funs, list) else list(funs.values())
def walk(o, path, hits):
    if isinstance(o, dict):
        for k, v in o.items():
            if k == 'BinaryOp' and isinstance(v, list) and v and json.dumps(v[0]).find('Sh') >= 0:
                hits.append((path, v))
            walk(v, path + [k], hits)
    elif isinstance(o, list):
        for i, v in enumerate(o): walk(v, path + [i], hits)
for f in funs:
    if f is None: continue
    nm = name_str(f['item_meta']['name'])
    if not any(n in nm for n in names): continue
    print('== fun', nm)
    safe = nm.replace('::', '__').replace('{', '').replace('}', '')
    with open(os.path.join(outd, 'NPE_llbc_' + safe + '.json'), 'w') as fh:
        json.dump(f, fh, indent=1)
    hits = []
    walk(f.get('body'), [], hits)
    body = f.get('body') or {}
    b = body.get('Unstructured', body.get('Structured', body))
    locs = None
    if isinstance(b, dict) and 'locals' in b:
        locs = b['locals']
    if locs is not None:
        lv = locs.get('locals', locs)
        print(' locals:')
        for l in lv:
            print('   ', json.dumps(l)[:400])
    for p, v in hits:
        print(' SHIFT BinaryOp:', json.dumps(v)[:2000])
