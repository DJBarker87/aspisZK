#!/usr/bin/env python3
"""List opaque layouts projected or constructed by selected transparent bodies."""
import json,sys
x=json.load(open(sys.argv[1]))['translated'];used=set()
def walk(v):
    if isinstance(v,dict):
        for k,w in v.items():
            if k=='Field' and isinstance(w,list) and isinstance(w[0],dict) and 'Adt' in w[0]:used.add(w[0]['Adt'][0])
            if k=='Aggregate' and isinstance(w,list) and isinstance(w[0],dict) and 'Adt' in w[0]:
                z=w[0]['Adt'][0]['id']
                if isinstance(z,dict) and 'Adt' in z:used.add(z['Adt'])
            walk(w)
    elif isinstance(v,list):
        for w in v:walk(w)
for f in x['fun_decls']:
    if f and f.get('body'):walk(f['body'])
rows=[dict(id=t['def_id'],name=t['item_meta']['name']) for t in x['type_decls'] if t and t['def_id'] in used and t['kind']=='Opaque']
print(json.dumps(rows,indent=2))
