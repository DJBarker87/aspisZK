#!/usr/bin/env python3
"""X2: direct callees of named functions in one Charon LLBC (reads only): every function declaration and global a
named function's body refers to (FunDeclId / GlobalDeclId anywhere in the body, including closures' and trait
method references by their impl's method id when resolved), with names. Used to add the callees of a function made
opaque as extra roots, so the reachable set below it stays in the emission. Runs inside a fv_slot.sh scope.
usage: fv_x2_callees.py <out.llbc> <out.json> <name-suffix>..."""
import json, sys
doc = json.load(open(sys.argv[1])); tr = doc.get('translated', doc)
def name(d):
    out = []
    for x in d['item_meta']['name']:
        out.append(x['Ident'][0] if 'Ident' in x else '{impl}' if 'Impl' in x else '{' + next(iter(x)) + '}')
    return '::'.join(out)
funs = {d['def_id']: d for d in tr['fun_decls'] if d}
globs = {d['def_id']: d for d in tr.get('global_decls', []) if d}
impls = {d['def_id']: d for d in tr.get('trait_impls', []) if d}
res = {}
def refs(x, acc):
    if isinstance(x, dict):
        for k, v in x.items():
            if k == 'Fun' and isinstance(v, int): acc['fun'].add(v)   # FnPtr: {"Regular": {"kind": {"Fun": <id>}, "generics": ...}}
            elif k == 'Regular' and isinstance(v, int): acc['fun'].add(v)
            elif k == 'Global' and isinstance(v, dict) and isinstance(v.get('id'), int): acc['glob'].add(v['id'])
            elif k == 'id' and isinstance(v, int) and 'generics' in x and 'Global' not in x: acc['maybe'].add(v)
            refs(v, acc)
    elif isinstance(x, list):
        for v in x: refs(v, acc)
for suffix in sys.argv[3:]:
    for i, d in funs.items():
        n = name(d)
        if not n.endswith(suffix): continue
        acc = dict(fun=set(), glob=set(), maybe=set()); refs(d.get('body'), acc)
        res[n] = dict(functions=sorted({name(funs[j]) for j in acc['fun'] if j in funs}), globals=sorted({name(globs[j]) for j in acc['glob'] if j in globs}))
json.dump(res, open(sys.argv[2], 'w'), indent=1)
for n, v in res.items():
    print('==', n); [print('  f', x) for x in v['functions']]; [print('  g', x) for x in v['globals']]
