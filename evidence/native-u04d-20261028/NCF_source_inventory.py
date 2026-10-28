"""Read frozen sources without visiting any other worktree. No proof credit."""
from pathlib import Path
import subprocess,json,hashlib,re
E=Path(__file__).resolve().parent
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def read(rev,p):return subprocess.check_output(['git','show',rev+':'+p],text=True)
def pin(s):return dict(sha256=hashlib.sha256(s.encode()).hexdigest(),bytes=len(s.encode()))
prior=json.loads(Path('evidence/native-tx2k-20261028/NBX_SOURCE_ASSOCIATION.json').read_text())
files={p:read(REV,p) for p in prior['files']}
modelpath='docs/research/100bit-spend-path-20261013/lean/AdapterRwModel.lean'
model=read('HEAD',modelpath)
assert pin(model)['sha256']==prior['sdk_model_sha256']
for p,s in files.items():assert pin(s)==prior['files'][p]
rows={}
# NBX's textual method-name search conflates V1 and V2 call points. Resolve by branch.
for slot in [15,23,25,26,27,28,29,30,31,32,33,34,48,49]:
 row=prior['slots'][str(slot)]
 native=[]
 for o in row['native_occurrences']:
  l=o['line'];p=o['path']
  if slot in [25,26,30] and l in [135,134,170,577,576,612]:continue
  if slot in [27,28,29] and l in [195,194,222,637,636,664]:continue
  native.append(dict(path=p,line=l,source_line=files[p].splitlines()[l-1]))
 sdk=[]
 for o in row['sdk_occurrences']:
  l=o['line'];assert 'ops.op'+str(slot) in model.splitlines()[l-1]
  sdk.append(dict(line=l,context='\n'.join(model.splitlines()[l-3:l+5])))
 rows[str(slot)]=dict(function=row['native_function'],native=native,sdk=sdk,status='OPEN; static association only')
# Exact early return prefixes from frozen bodies; no slice payload operation precedes the length check.
reject={}
for slot,filename,fn,size,bound in [(23,'pair_forest_terminal.rs','decode_pool_v1_pair_forest_terminal_request_v1',320,321),(31,'verifier_registry.rs','decode_verifier_registry_v1',128,129),(32,'verifier_registry.rs','decode_verifier_registry_entry_v1',192,193),(33,'verifier_registry.rs','decode_verifier_registry_v2',256,257),(34,'verifier_registry.rs','decode_verifier_registry_entry_v2',320,321)]:
 p='crates/aspis-statement/src/pool_v1/'+filename;s=files[p];start=s.index('pub fn '+fn+'(');body=s[start:];m=re.search(r'\{\s*if bytes.len\(\) != ([A-Z0-9_]+) \{\s*return Err\(([^;]+)\);\s*\}',body)
 assert m,(slot,body[:500])
 reject[str(slot)]=dict(path=p,line=s[:start].count('\n')+1,prefix=body[:m.end()],constant=m[1],expected_size=size,inherited_inclusive_bound=bound,error=m[2],status='source inspection; native arbitrary-length gate not run')
out=dict(frozen_revision=REV,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),files={p:pin(s) for p,s in files.items()},sdk_model=dict(path=modelpath,**pin(model)),slots=rows,rejection=reject,axioms='N/A: no new theorem or prover run',finding='V1/V2 overloaded method occurrences are separated by actual branch; inherited textual matches are not typed association proofs')
(E/'NCF_SOURCE_INVENTORY.json').write_text(json.dumps(out,indent=2)+'\n')
print('14 slot rows and 5 early-rejection prefixes pinned; no native closure credit')
