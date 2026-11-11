#!/usr/bin/env python3
"""Translatability pass, worker 3: structural scan of one LLBC file for mutable-borrow type arguments with an
erased region (the shape behind the reported dropped write through `iter_mut().rev()`), and a completeness
check of an Aeneas emission against Charon's declaration list.
usage: tp3_erased_scan.py <out.llbc> [<emitted Funs.lean> <crate-name>]
Prints JSON: {erased_mut_type_args: [{function, type_arg}], declarations, missing_from_emission: [...]}"""
import json, re, sys
d = json.load(open(sys.argv[1])); tr = d.get('translated', d)
types = {}
def collect(x):
    if isinstance(x, dict):
        if 'Value' in x and isinstance(x['Value'], list) and len(x['Value']) == 2 and isinstance(x['Value'][0], int):
            types[x['Value'][0]] = x['Value'][1]
        for v in x.values(): collect(v)
    elif isinstance(x, list):
        for v in x: collect(v)
collect(tr)
def resolve(t):
    while isinstance(t, dict) and ('Deduplicated' in t or ('Value' in t and isinstance(t['Value'], list))):
        t = types.get(t['Deduplicated']) if 'Deduplicated' in t else t['Value'][1]
    return t
memo = {}
def has_erased_mut(t, depth=0):
    key = None
    if isinstance(t, dict) and 'Deduplicated' in t: key = t['Deduplicated']
    elif isinstance(t, dict) and 'Value' in t and isinstance(t['Value'], list) and len(t['Value']) == 2 and isinstance(t['Value'][0], int): key = t['Value'][0]
    if key is not None:
        if key in memo: return memo[key]
        memo[key] = False
        r = has_erased_mut(types.get(key), depth + 1)
        memo[key] = r
        return r
    if depth > 200: return False
    if isinstance(t, dict):
        if 'Ref' in t and isinstance(t['Ref'], list) and len(t['Ref']) == 3:
            r, inner, kind = t['Ref']
            if kind == 'Mut' and r == 'Erased': return True
            return has_erased_mut(inner, depth + 1)
        return any(has_erased_mut(v, depth + 1) for v in t.values())
    if isinstance(t, list): return any(has_erased_mut(v, depth + 1) for v in t)
    return False
def name(meta):
    out = []
    for x in meta['name']:
        out.append(x['Ident'][0] if 'Ident' in x else '{impl}' if 'Impl' in x else '{%s}' % next(iter(x)))
    return '::'.join(out)
hits = []
def walk(x, fn):
    if isinstance(x, dict):
        if 'regions' in x and 'types' in x and isinstance(x['types'], list):
            for ty in x['types']:
                if has_erased_mut(ty): hits.append(dict(function=fn, type_arg=json.dumps(resolve(ty))[:200]))
        for v in x.values(): walk(v, fn)
    elif isinstance(x, list):
        for v in x: walk(v, fn)
decls = []
for f in tr['fun_decls']:
    if not f: continue
    n = name(f['item_meta']); decls.append((n, f['item_meta'].get('is_local'), f.get('body') not in (None, 'Opaque')))
    if f.get('body') not in (None, 'Opaque'): walk(f['body'], n)
res = dict(llbc=sys.argv[1], erased_mut_type_args=hits, declarations=len(decls))
if len(sys.argv) > 3:
    # Completeness by source span: every local function with a body in Charon's output must have an emitted Lean
    # definition whose doc comment names the same file and start line (Aeneas writes "Source: '<file>', lines
    # L:C-..." for every definition, plus the macro invocation line for macro-generated items; loop bodies add
    # entries, never fewer). A closure's call_once and call_mut are not counted separately from its call.
    import collections
    lean = open(sys.argv[2]).read()
    files = tr['files']
    def fname(i):
        f = files[i]; n = f['name'] if isinstance(f, dict) else f
        if isinstance(n, dict): n = list(n.values())[0]
        return str(n)
    emitted = collections.Counter((f, l) for f, l, _ in re.findall(r"Source: '([^']+)', lines (\d+):(\d+)-", lean))
    emitted.update((f, l) for f, l in re.findall(r"macro invocation at: '([^']+)', lines (\d+):\d+-", lean))
    want = collections.Counter(); names = {}
    for f in tr['fun_decls']:
        if not f or not f['item_meta'].get('is_local') or f.get('body') in (None, 'Opaque'): continue
        sp = f['item_meta']['span']; sp = sp.get('Untagged', sp); sp = sp.get('data', sp)
        n = name(f['item_meta'])
        # A closure's call_once and call_mut are emitted as instance fields over its single `call`.
        if re.search(r'::\{impl\}::call_(once|mut)$', n): continue
        key = (fname(sp['file_id']), str(sp['beg']['line']))
        want[key] += 1; names.setdefault(key, []).append(name(f['item_meta']))
    missing = [dict(source='%s:%s' % k, names=names[k], charon=v, emitted=emitted.get(k, 0)) for k, v in sorted(want.items()) if emitted.get(k, 0) < v]
    res.update(local_transparent=sum(want.values()), missing_from_emission=missing)
print(json.dumps(res, indent=1))
