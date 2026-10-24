"""Read-only exact Drop/glue inventory of retained selected64 LLBC."""
from pathlib import Path
import collections
import hashlib
import json
D = Path(__file__).resolve().parent
R = D.parents[2]
P = D.parent/'rng-extractor/ProverRwRngExtractorselected64.llbc'
x = json.loads(P.read_text())['translated']
cons = {}
def collect(o):
    if isinstance(o, dict):
        if 'HashConsedValue' in o:
            k,v = o['HashConsedValue']; cons[k] = v
        for v in o.values(): collect(v)
    elif isinstance(o,list):
        for v in o: collect(v)
collect(x)
def expand(o, depth=0):
    if depth > 150: raise ValueError('unexpected recursive hashcons')
    if isinstance(o,dict):
        if 'Deduplicated' in o: return expand(cons[o['Deduplicated']], depth+1)
        if 'HashConsedValue' in o: return expand(o['HashConsedValue'][1], depth+1)
        return {k:expand(v,depth+1) for k,v in o.items()}
    if isinstance(o,list): return [expand(v,depth+1) for v in o]
    return o
names = {t['def_id']:t['item_meta']['name'] for t in x['type_decls'] if t}
def name(n):
    return '::'.join(str(e['Ident'][0]) if 'Ident' in e else json.dumps(e,sort_keys=True) for e in n)
def ty(o):
    if not isinstance(o,dict): return str(o)
    if 'Adt' in o:
        a=o['Adt']; k=a['id']; n=name(names[k['Adt']]) if isinstance(k,dict) and 'Adt' in k else str(k)
        args=[ty(v) for v in a['generics']['types']]
        args += [json.dumps(v,sort_keys=True) for v in a['generics']['const_generics']]
        return n+('<'+', '.join(args)+'>' if args else '')
    if 'Ref' in o:
        _,t,mut=o['Ref']; return '&'+('mut ' if mut=='Mut' else '')+ty(t)
    if 'Var' in o:return 'generic '+json.dumps(o['Var'],sort_keys=True)
    if 'Literal' in o:return str(o['Literal'])
    return json.dumps(o,sort_keys=True)
rows=[]
def walk(o,f,path):
    if isinstance(o,dict):
        if 'Drop' in o:
            drop=expand(o['Drop'])
            rows.append(dict(function_id=f['def_id'],function=name(f['item_meta']['name']),
                json_path=path, type=ty(drop['place']['ty']),drop=drop))
        for k,v in o.items(): walk(v,f,path+'/'+k)
    elif isinstance(o,list):
        for i,v in enumerate(o):walk(v,f,path+'/'+str(i))
for f in x['fun_decls']:
    if f and f.get('body'): walk(f['body'],f,'body')
counts=collections.Counter(r['type'] for r in rows)
out=dict(schema='ProverRwNativeEntropy-drop-inventory-v1',input_sha256=hashlib.sha256(P.read_bytes()).hexdigest(),
    input_bytes=P.stat().st_size,drop_count=len(rows),types=dict(counts),sites=rows,
    limitation='Inventory of retained selected crate, not a transitive destructor implementation or whole-owner extraction. Conditional unwind branches counted as distinct statements.',
    print_axioms='N/A: read-only source inventory')
O=R/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/native-entropy'
O.mkdir(parents=True,exist_ok=True)
(O/'selected-drop-inventory.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out['types'],indent=2))
