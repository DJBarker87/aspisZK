#!/usr/bin/env python3
"""X2: size census of one Charon LLBC (reads only). For every function and global declaration: name, source span,
serialized size of its body in bytes, and whether it has a body; plus totals per crate. Used to locate the declarations
that make the LLBC (and Aeneas' memory) large before choosing what to isolate. Runs inside a fv_slot.sh scope.
usage: fv_x2_llbc_sizes.py <out.llbc> <out.json>"""
import collections, json, sys
doc = json.load(open(sys.argv[1])); tr = doc.get('translated', doc)
files = {f['id']: (f['name'].get('Local') or f['name'].get('Virtual') or str(f['name'])) for f in tr.get('files', []) if f}
def name(d):
    out = []
    for x in d['item_meta']['name']:
        out.append(x['Ident'][0] if 'Ident' in x else '{impl}' if 'Impl' in x else '{' + next(iter(x)) + '}')
    return '::'.join(out)
def span(d):
    s = d['item_meta'].get('span') or {}
    dd = (s.get('Untagged') or s).get('data') or s.get('data') or {}
    return '%s:%s' % ((files.get(dd.get('file_id')) or '').split('/src/')[-1], (dd.get('beg') or {}).get('line'))
rows = []
for kind in ('fun_decls', 'global_decls', 'type_decls', 'trait_impls', 'trait_decls'):
    for d in tr.get(kind, []):
        if not d: continue
        b = d.get('body'); size = len(json.dumps(b)) if b is not None else len(json.dumps(d))
        rows.append(dict(kind=kind, name=name(d), span=span(d), size=size, body=isinstance(b, dict) and 'Structured' in b if kind == 'fun_decls' else None))
tot = collections.Counter(); per = collections.Counter()
for r in rows: tot[r['kind']] += r['size']; per[r['name'].split('::')[0]] += r['size']
other = {k: len(json.dumps(v)) for k, v in tr.items() if k not in ('fun_decls', 'global_decls', 'type_decls', 'trait_impls', 'trait_decls')}
rows.sort(key=lambda r: -r['size'])
json.dump(dict(totals_by_kind=tot, totals_by_crate=per, other_tables=other, top=rows[:200], all=rows), open(sys.argv[2], 'w'), indent=1)
print('by kind', dict(tot)); print('by crate', per.most_common(12)); print('other', other)
for r in rows[:40]: print(r['size'], r['kind'], r['name'], r['span'])
