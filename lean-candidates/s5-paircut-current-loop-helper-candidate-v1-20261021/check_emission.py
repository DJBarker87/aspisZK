#!/usr/bin/env python3
"""Check Charon source-text coverage for the exact current Pair/helper bodies."""
from pathlib import Path
import hashlib, json, sys

P=Path(__file__).resolve().parent
pins=json.loads((P/'input/source-pins.json').read_text())
source=(P/'input/candidate-weights.rs').read_text()
llbc_path=Path(sys.argv[1])
llbc_bytes=llbc_path.read_bytes()
assert hashlib.sha256(llbc_bytes).hexdigest()==sys.argv[2], 'LLBC hash differs from selected extraction receipt'
d=json.loads(llbc_bytes)
assert d.get('has_errors') is False
t=d['translated']
assert t.get('ordered_decls'), 'ordered declaration list is empty'

def ident(e):
    return e.get('Ident',[None])[0] if isinstance(e,dict) else None

def is_weights_pair(x, name):
    path=x['item_meta']['name']
    return (ident(path[0])=='aspis_r1_cost_probe' and ident(path[1])=='weights'
            and ident(path[-1])==name and any('Impl' in e for e in path))

expected=('push_byte_products_row','push_byte_products_partial','push_byte_products_high','pair')
found={}
for f in t['fun_decls']:
    if not isinstance(f,dict):
        continue
    meta=f.get('item_meta') or {}
    for name in expected:
        if is_weights_pair(f,name):
            found.setdefault(name,[]).append(f)
assert set(found)==set(expected), {k:len(v) for k,v in found.items()}
report={'schema':'s5-paircut-current-helper-llbc-source-coverage-v1',
        'llbc_sha256':hashlib.sha256(llbc_bytes).hexdigest(),'llbc_bytes':len(llbc_bytes),
        'has_errors':d['has_errors'],'ordered_decl_groups':len(t['ordered_decls']),
        'fun_decls':len(t['fun_decls']),'type_decls':len(t['type_decls']),
        'source_methods':{}}
for name,fs in found.items():
    assert len(fs)==1,(name,len(fs))
    text=fs[0]['item_meta'].get('source_text')
    assert isinstance(text,str) and text and text in source, f'{name} extracted source_text does not match candidate source bytes'
    report['source_methods'][name]={'def_id':fs[0]['def_id'],'source_text_sha256':hashlib.sha256(text.encode()).hexdigest(),
                                    'source_text_bytes':len(text.encode()),'candidate_contains_exact_source_text':True}
print(json.dumps(report,indent=2,sort_keys=True))
