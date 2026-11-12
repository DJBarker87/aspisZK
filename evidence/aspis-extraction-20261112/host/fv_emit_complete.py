#!/usr/bin/env python3
"""X7 gate (ii): per crate, every function with a body in the Charon output (LLBC `fun_decls` whose body is
`Structured`) is emitted (a definition in the raw Funs.lean with the same source file and first line, the rule of
TP_llbc_scan.py; or, for items whose span is a macro invocation, the same file and the same Rust path after every
`{...}` impl segment is written `{impl}`) or is listed by name as not emitted with the reason:
  opaque by flag        an axiom in the external template and named by the config's opaque list
  derived impl          a derived clone/eq/ne/fmt/default/hash method that no emitted definition refers to
  builtin item          a compiler-generated `{Builtin}` item (drop glue and the like)
  not in ordered_decls  Charon translated the body but the item is not in Charon's ordered declaration list
                        (unreachable after Charon's passes; Aeneas extracts only listed groups)
  dropped by Aeneas     in ordered_decls, non-local, no emitted definition refers to it
  FAILURE               referenced by an emitted definition with no definition, or bodiless without being named opaque
Pass iff no FAILURE row. Reads only.
usage: fv_emit_complete.py <out.llbc> <raw dir> <program config.json>   (TSV on stdout; summary and gate line last)"""
import json, re, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from fv_emit_lean import blocks, rel


def norm(rust):
    out, depth, buf = [], 0, ''
    for ch in rust:
        if ch == '{':
            if depth == 0:
                buf += '{impl}'
            depth += 1
        elif ch == '}':
            depth -= 1
        elif depth == 0:
            buf += ch
    return re.sub(r'<[^<>]*>', '', buf)


def nm(name):
    out = []
    for e in name:
        if 'Ident' in e: out.append(e['Ident'][0])
        elif 'Impl' in e: out.append('{impl}')
        elif 'Monomorphized' in e: pass
        else: out.append('{%s}' % next(iter(e)))
    return '::'.join(out)


LL, R, cfg = Path(sys.argv[1]), Path(sys.argv[2]), json.loads(Path(sys.argv[3]).read_text())
doc = json.load(open(LL))
tr = doc['translated']
files = {f['id']: (f['name'].get('Local') or f['name'].get('Virtual') or str(f['name'])) for f in tr['files'] if f}
HC = {}
stack = [tr]
while stack:
    x = stack.pop()
    if isinstance(x, dict):
        for k, v in x.items():
            if k in ('HashConsedValue', 'Value') and isinstance(v, list) and len(v) == 2 and isinstance(v[0], int): HC[v[0]] = v[1]
            stack.append(v)
    elif isinstance(x, list): stack.extend(x)


def span(f):
    s = f['item_meta']['span']
    s = s.get('Untagged', s)
    if 'Deduplicated' in s: s = HC.get(s['Deduplicated'], s)
    if isinstance(s, dict) and 'Value' in s: s = s['Value'][1]
    s = s.get('data', s)
    return rel(files.get(s.get('file_id'), '')), (s.get('beg') or {}).get('line')


ordered = set()
def collect_ids(x):
    if isinstance(x, dict):
        for k, v in x.items():
            if k == 'Fun':
                stack2 = [v]
                while stack2:
                    y = stack2.pop()
                    if isinstance(y, int): ordered.add(y)
                    elif isinstance(y, dict): stack2.extend(y.values())
                    elif isinstance(y, list): stack2.extend(y)
            else:
                collect_ids(v)
    elif isinstance(x, list):
        for v in x: collect_ids(v)
collect_ids(tr.get('ordered_decls', []))
funs = [b for b in blocks(R / 'Funs.lean') if b['kind'] and b['kind'] != 'axiom']
ext = blocks(R / 'FunsExternal_Template.lean')
emitted = {(rel(b['file']), b['a']) for b in funs}
emitted_names = {(rel(b['file']), norm(b['rust'])) for b in funs}
ext_spans = {(rel(b['file']), b['a']) for b in ext}
code = re.sub(r'(?s)/--.*?-/', '', (R / 'Funs.lean').read_text())
own = cfg['own_crate']
opq = [o.replace('crate::', own + '::') for o in cfg['opaque']]


def is_opaque(n):
    p = n.split('::')
    for o in opq:
        q = o.split('::')
        if p[0] == q[0] and p[-1] == q[-1] and all(x in p for x in q[1:-1] if x != '_' and not x.startswith('{')):
            return True
    return False


rows, summary, fail = [], {}, 0
for f in tr['fun_decls']:
    if not f:
        continue
    n = nm(f['item_meta']['name'])
    crate = next((c for c in cfg['crates'] if n.startswith(c + '::')), None)
    body = f.get('body')
    if crate is None or not (isinstance(body, dict) and 'Structured' in body):
        continue
    s = summary.setdefault(crate, {'with_body': 0, 'emitted': 0})
    s['with_body'] += 1
    fl, ln = span(f)
    if (fl, ln) in emitted or (fl, norm(n)) in emitted_names:
        s['emitted'] += 1
        continue
    last = n.split('::')[-1]
    mod = [x for x in n.split('::') if not x.startswith('{')][-2] if len([x for x in n.split('::') if not x.startswith('{')]) > 1 else ''
    referenced = bool(re.search(r'\b%s\.(?:[A-Za-z0-9_]+\.)*%s\b(?!\.closure)' % (re.escape(mod), re.escape(last)), code)) if mod else False
    if (fl, ln) in ext_spans:
        why = 'opaque by flag' if is_opaque(n) else 'FAILURE: bodiless in the external template, not named opaque'
    elif '{Builtin}' in n:
        why = 'builtin item (drop glue or the like)'
    elif re.search(r'\{impl\}::(clone|eq|ne|fmt|default|hash)$', n) and not referenced:
        why = 'derived impl, ' + ('not in ordered_decls' if f['def_id'] not in ordered else 'dropped by Aeneas')
    elif referenced and f['def_id'] in ordered:
        why = 'FAILURE: an emitted definition refers to it and it has no definition'
    elif f['def_id'] not in ordered:
        why = 'not in ordered_decls (Charon-unreachable after its passes)'
    else:
        why = 'dropped by Aeneas (in ordered_decls, no emitted definition refers to it)'
    key = why.split(' (')[0].split(',')[0].split(':')[0]
    s[key] = s.get(key, 0) + 1
    fail += why.startswith('FAILURE')
    rows.append((crate, n, '%s:%s' % (fl, ln), why))
print('crate\tfunction\tfile:line\treason')
for r in sorted(rows):
    print('\t'.join(map(str, r)))
for c in cfg['crates']:
    print('# %s %s' % (c, json.dumps(summary.get(c, {}))))
print('gate (ii) every function with a body emitted or listed with a reason: %s (%d FAILURE rows)' % ('pass' if fail == 0 else 'FAIL', fail))
sys.exit(0 if fail == 0 else 1)
