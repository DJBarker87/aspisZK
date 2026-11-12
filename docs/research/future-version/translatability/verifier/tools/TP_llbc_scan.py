#!/usr/bin/env python3
"""Aspis translatability pass: two checks on one Charon output and the Aeneas emission made from it. Reads only.
 1. Completeness: every function Charon lists with a body, in the given crates, must have an emitted `def` (or be an
    axiom of the external template, which is then reported). Matching is by source file and first line.
 2. Dropped-write shape: every generic instantiation (of a call or a function reference) whose TYPE arguments contain
    a mutable borrow with an ERASED region. The emitted Lean for such a call cannot say which borrow the written
    values go back to (the defect the privacy lead's combined tool rejects as PV-ITERMUT).
usage: TP_llbc_scan.py <charon run dir> <aeneas raw dir or -> <json-out> <crate prefix>..."""
import json, re, sys
from pathlib import Path
crun, raw, outj = Path(sys.argv[1]), sys.argv[2], sys.argv[3]; crates = tuple(sys.argv[4:])
doc = json.load(open(crun / 'out.llbc')); tr = doc.get('translated', doc)
files = {f['id']: (f['name'].get('Local') or f['name'].get('Virtual') or str(f['name'])) for f in tr.get('files', []) if f}
types = {}
def collect(x):
    if isinstance(x, dict):
        if set(x) == {'Value'} and isinstance(x['Value'], list) and len(x['Value']) == 2 and isinstance(x['Value'][0], int): types[x['Value'][0]] = x['Value'][1]
        for v in x.values(): collect(v)
    elif isinstance(x, list):
        for v in x: collect(v)
collect(tr)
def res(t):
    while isinstance(t, dict) and set(t) in ({'Deduplicated'}, {'Value'}):
        t = types.get(t['Deduplicated']) if 'Deduplicated' in t else t['Value'][1]
    return t
_memo_me = {}
def _tid(t):
    if isinstance(t, dict):
        if set(t) == {'Deduplicated'}: return t['Deduplicated']
        if set(t) == {'Value'} and isinstance(t['Value'], list) and len(t['Value']) == 2 and isinstance(t['Value'][0], int): return t['Value'][0]
    return None
def mut_erased(t, depth=0, seen=None):
    """does the type contain `&mut` with an erased region"""
    i = _tid(t)
    if i is not None:
        if i in _memo_me: return _memo_me[i]
        _memo_me[i] = False
        r = _mut_erased(res(t), depth); _memo_me[i] = r; return r
    return _mut_erased(t, depth)
def _mut_erased(t, depth=0):
    if depth > 40: return False
    if isinstance(t, dict):
        if 'Ref' in t and isinstance(t['Ref'], list) and len(t['Ref']) == 3:
            reg, inner, kind = t['Ref']
            if kind == 'Mut' and reg == 'Erased': return True
            return mut_erased(inner, depth + 1)
        return any(mut_erased(v, depth + 1) for v in t.values())
    if isinstance(t, list): return any(mut_erased(v, depth + 1) for v in t)
    return False
# type declarations that hold a mutable borrow under one of their own region parameters (IterMut, ChunksExactMut, ...)
tdecl = {d['def_id']: d for d in tr.get('type_decls', []) if d}
_holds = {}
def holds_mut(tid, depth=0):
    if tid in _holds: return _holds[tid]
    _holds[tid] = False
    d = tdecl.get(tid)
    if d is None or depth > 6: return False
    def any_mut(x, dd=0):
        x = res(x)
        if dd > 30: return False
        if isinstance(x, dict):
            if 'Ref' in x and isinstance(x['Ref'], list) and len(x['Ref']) == 3:
                if x['Ref'][2] == 'Mut': return True
                return any_mut(x['Ref'][1], dd + 1)
            if 'Adt' in x and isinstance(x['Adt'], dict):
                i = x['Adt'].get('id'); i = i.get('Adt') if isinstance(i, dict) else None
                if i is not None and holds_mut(i, depth + 1): return True
            return any(any_mut(v, dd + 1) for v in x.values())
        if isinstance(x, list): return any(any_mut(v, dd + 1) for v in x)
        return False
    _holds[tid] = any_mut(d.get('kind'))
    return _holds[tid]
_memo_ae = {}
def adt_mut_erased(t, depth=0):
    """does the type contain an ADT that holds a mutable borrow and is instantiated with an erased region"""
    i = _tid(t)
    if i is not None:
        if i in _memo_ae: return _memo_ae[i]
        _memo_ae[i] = False
        r = _adt_mut_erased(res(t), depth); _memo_ae[i] = r; return r
    return _adt_mut_erased(t, depth)
def _adt_mut_erased(t, depth=0):
    if depth > 40: return False
    if isinstance(t, dict):
        if 'Adt' in t and isinstance(t['Adt'], dict):
            i = t['Adt'].get('id'); i = i.get('Adt') if isinstance(i, dict) else None
            g = t['Adt'].get('generics') or {}
            if i is not None and 'Erased' in [r for r in g.get('regions', []) if isinstance(r, str)] and holds_mut(i): return True
        return any(adt_mut_erased(v, depth + 1) for v in t.values())
    if isinstance(t, list): return any(adt_mut_erased(v, depth + 1) for v in t)
    return False
def name(f):
    out = []
    for x in f['item_meta']['name']:
        out.append(x['Ident'][0] if 'Ident' in x else '{impl}' if 'Impl' in x else '{' + next(iter(x)) + '}')
    return '::'.join(out)
def span(f):
    s = f['item_meta'].get('span') or {}
    d = (s.get('Untagged') or s).get('data') or s.get('data') or {}
    return files.get(d.get('file_id')), (d.get('beg') or {}).get('line')
funs = [f for f in tr['fun_decls'] if f]
hits = []
def walk(x, fn, path):
    if isinstance(x, dict):
        if _tid(x) is not None: return    # a type: checked where it is a type argument, not walked as code
        if 'types' in x and 'regions' in x and isinstance(x['types'], list):
            for i, ty in enumerate(x['types']):
                if mut_erased(ty) or adt_mut_erased(ty): hits.append(dict(function=fn, where=path[-3:], type_argument=i))
        for k, v in x.items(): walk(v, fn, path + [k])
    elif isinstance(x, list):
        for v in x: walk(v, fn, path)
for f in funs:
    n = name(f)
    if n.startswith(crates) and isinstance(f.get('body'), dict): walk(f['body'], n, [])
dedup = {}
for h in hits: dedup.setdefault(h['function'], 0); dedup[h['function']] += 1
missing = []; emitted = set(); axioms = set()
if raw != '-':
    for src, bag in (('Funs.lean', emitted), ('FunsExternal_Template.lean', axioms)):
        p = Path(raw) / src
        if not p.exists(): continue
        for m in re.finditer(r"(?m)^/-- \[[^\n]*\n\s+Source: '([^']*)', lines (\d+):", p.read_text()): bag.add((m.group(1), int(m.group(2))))
    for f in funs:
        n = name(f); fl, ln = span(f)
        body = f.get('body'); kind = next(iter(body)) if isinstance(body, dict) else body
        if not n.startswith(crates) or kind != 'Structured' or fl is None: continue
        if (fl, ln) in emitted: continue
        missing.append(dict(function=n, file=fl, line=ln, status='axiom in the external template' if (fl, ln) in axioms else 'NOT EMITTED'))
res_ = dict(functions_with_body=sum(1 for f in funs if name(f).startswith(crates) and isinstance(f.get('body'), dict)), mutable_borrow_type_arguments_with_erased_region=dedup, not_emitted=missing)
json.dump(res_, open(outj, 'w'), indent=1)
print('functions with a body in', crates, ':', res_['functions_with_body'])
print('functions with a mutable-borrow type argument under an erased region:', len(dedup)); [print('   ', k, v) for k, v in sorted(dedup.items())]
print('Structured in Charon, no emitted definition:', len(missing)); [print('   ', m['status'], '|', m['function'], m['file'].split('/src/')[-1], m['line']) for m in missing[:60]]
