"""Read-only assessment of existing054 source/MIR-derived packet; no extraction."""
from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent;ROOT=D.parents[2]
E=ROOT/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023'
p=E/'factory-state/emission-audit.json';j=json.loads(p.read_text());r=j['selected_resume'];b=r['body']['Structured']['body'];f=next(f for f in j['functions'] if f['id']==0)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=(D/'proof/selected.rs').read_text();before=(D.parent/'factory-state/preflight/lib.rs').read_text()
assert source==before.replace('ProverRwFactoryState','ProverRwResumeScalar')
assert r['item_meta']['source_text'].replace('ProverRwFactoryState','ProverRwResumeScalar') in source
locals=r['body']['Structured']['locals']['locals']
assert {l['index']:l['name'] for l in locals if l['name']}=={1:'self',2:'request',3:'bytes',4:'outcome',5:'error',10:'field_mask_entropy',12:'leaf_salt_seed'}
normal=[d for d in f['drops'] if not d['in_unwind']]
assert [(d['statement_id'],d['place']['kind']) for d in normal]==[(430,{'Local':12}),(441,{'Local':10}),(448,{'Local':3}),(544,{'Local':12}),(555,{'Local':10}),(562,{'Local':3}),(607,{'Local':3})]
for d in normal:assert d['fn_ptr']['kind']=={'Fun':{'Regular':15}}
ok=b['statements'][8]['kind']['Switch']['Match'][1][0][1]['statements']
accepted=ok[93]['kind']['Switch']['If'][1]['statements'][14]['kind']['Switch']['If'][1]
assert accepted['statements']==[]
def walk(x,path=''):
 if isinstance(x,dict):
  if 'id' in x and 'kind' in x:yield path,x
  for k,v in x.items():
   if k!='on_unwind':yield from walk(v,path+'/'+k)
 elif isinstance(x,list):
  for i,v in enumerate(x):yield from walk(v,path+'/'+str(i))
statements=dict((x['id'],(path,x)) for path,x in walk(b) if isinstance(x.get('id'),int))
selected=[]
for ident in [4,6,8,380,382,386,430,441,448,494,496,544,555,562,607]:
 if ident in statements:
  path,x=statements[ident];selected.append(dict(path=path,statement=x))
out=dict(schema='ProverRwResumeScalar-reused-bindings-v1',command=['python3',str(D/'reuse-bindings.py')],input_sha256={str(p.relative_to(ROOT)):sha(p),str((D.parent/'factory-state/preflight/lib.rs').relative_to(ROOT)):sha(D.parent/'factory-state/preflight/lib.rs'),str((D/'proof/selected.rs').relative_to(ROOT)):sha(D/'proof/selected.rs')},old_extraction_input=j['input'],old_source_map_sha256=j['source_map_sha256'],source_assessment='Full selected source identical under private-prefix rename; old054 is reused source association only, not new identity or closure gate',locals=[l for l in locals if l['name']],normal_drops=normal,selected_statements=selected,success_obstruction=dict(path='/Structured/body/statements/8/kind/Switch/Match/1/0/1/statements/93/kind/Switch/If/1/statements/14/kind/Switch/If/1',recorded_branch=accepted,consequence='This packet supplies no concrete success aggregate field-move witness. Do not infer missing native/source-role closure from rejection bindings. No claim that Rust success execution is empty or impossible.'),new_MIR_compile='admission denied, zero compiler invocations',scope='Rejection local identity/drop order and retry-before-drop binding only; success and native draw/returned-disposal roles remain source-inspected',print_axioms='N/A: read-only packet assessment',actual_extraction_invocations=0)
(E/'resume-scalar/reused-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
print('Recorded old054 local/drop bindings and missing success witness; no closure claim')
