"""Read-only source/callgraph audit; no claimed source-to-event theorem."""
from pathlib import Path
import hashlib,json,collections
D=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
p=D/'ProverRwOwnedDropFocused.llbc';j=json.loads(p.read_text())['translated']
cons={}
def gather(x):
    if isinstance(x,dict):
        if 'HashConsedValue' in x:
            k,v=x['HashConsedValue'];cons[k]=v
        for v in x.values():gather(v)
    elif isinstance(x,list):
        for v in x:gather(v)
def expand(x):
    if isinstance(x,dict):
        if 'Deduplicated' in x:return expand(cons[x['Deduplicated']])
        if 'HashConsedValue' in x:return expand(x['HashConsedValue'][1])
        return {k:expand(v) for k,v in x.items()}
    if isinstance(x,list):return [expand(v) for v in x]
    return x
gather(j)
j=expand(j)
rows=[]
def walk(x,path=''):
    if isinstance(x,dict):
        yield path,x
        for k,v in x.items():yield from walk(v,path+'/'+k)
    elif isinstance(x,list):
        for i,v in enumerate(x):yield from walk(v,path+'/'+str(i))
for f in j['fun_decls']:
    if not f:continue
    m=f['item_meta'];calls=[];drops=[]
    for path,x in walk(f['body']):
        if 'Call' in x:calls.append({'path':path,'call':x['Call']})
        if 'Drop' in x:drops.append({'path':path,'drop':x['Drop']})
    ref_outputs=[path for path,x in walk(f['signature']['output']) if 'Ref' in x]
    rows.append(dict(id=f['def_id'],name=m['name'],source_span=m['span'],body='opaque' if f['body']=='Opaque' else 'structured',signature=f['signature'],reference_output_paths=ref_outputs,calls=calls,drops=drops))
out=dict(schema='ProverRwOwnedDrop-source-audit-v1',input_sha256=sha(p),input_bytes=p.stat().st_size,functions=rows,claim='Actual zeroize dependency bodies exposed; existing private backend preflight rejects required iterator reference outputs and unsupported Drop shapes. No Lean emission or whole-owner/source-event theorem.',print_axioms='N/A: source audit; no Lean theorem')
(D/'source-audit.json').write_text(json.dumps(out,indent=2)+'\n')
# Read selected inventory without rewriting it.
R=D.parents[2]
old=R/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/native-entropy/selected-drop-inventory.json'
a=json.loads(old.read_text());sel=R/'tools/prover-rw-20261023/rng-extractor/ProverRwRngExtractorselected64.llbc'
S=json.loads(sel.read_text())['translated'];selected=[]
for f in S['fun_decls']:
    if f and 'generate_for_mask_nonce' in str(f['item_meta']['name']):selected.append(f)
(D/'selected64-source-audit.json').write_text(json.dumps(dict(selected_sha256=sha(sel),selected_bytes=sel.stat().st_size,inventory_sha256=sha(old),drop_count=a['drop_count'],types=a['types'],generate_for_mask_nonce=selected,claim='Exact source/control evidence retained, not a cleanup/event proof. Generic captured Drop and unwind remain open.',print_axioms='N/A: source audit'),indent=2)+'\n')
print(json.dumps({'functions':len(rows),'reference_returning_functions':[r['id'] for r in rows if r['reference_output_paths']],'selected_generate_functions':len(selected)}))
