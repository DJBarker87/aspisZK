#!/usr/bin/env python3
"""Read/hash-only verification of the one-sided common-module naming gate."""
from pathlib import Path,PurePosixPath
import hashlib,importlib.util,json,re,subprocess,tarfile
here=Path(__file__).resolve().parent;root=here.parents[4]
sha=lambda b:hashlib.sha256(b).hexdigest()
digest=lambda x:sha(json.dumps(x,sort_keys=True).encode())
m=json.loads((here/'manifest.json').read_text());archive=here/m['archive']
assert sha(archive.read_bytes())==m['archive_sha256'] and archive.stat().st_size==m['archive_bytes']
def read_tar(path):
 with tarfile.open(path,'r:gz') as t:
  ms=t.getmembers();assert len(set(x.name for x in ms))==len(ms)
  for x in ms:
   p=PurePosixPath(x.name);assert not p.is_absolute() and '..' not in p.parts
   assert x.isfile() or x.islnk()
   if x.islnk():assert x.linkname in t.getnames()
  return {x.name:t.extractfile(x).read() for x in ms}
data=read_tar(archive);assert len(data)==m['archive_entries']
entries={s.split('  ',1)[1]:s.split('  ',1)[0] for s in data['SHA256SUMS'].decode().splitlines()}
assert set(entries)==set(data)-{'SHA256SUMS'}
for n,h in entries.items():assert sha(data[n])==h,n
j=lambda n:json.loads(data[n])
prior={}
for name in ['decoder-public-binding-20261016','public-preparation-step-20261016']:
 p=here.parent/name;pm=json.loads((p/'manifest.json').read_text());pa=p/pm['archive']
 assert sha(pa.read_bytes())==pm['archive_sha256'];prior[name]=read_tar(pa)
limits={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0'}
reports=[];count=0
for group,rs in m['lean_receipts'].items():
 snapshot=j(group+'/external-inputs.json');keys={};visiting=set()
 def key(n):
  if n in keys:return keys[n]
  assert n not in visiting;visiting.add(n);x=snapshot['modules'][n]
  keys[n]=digest({'source':x['source_sha256'],'objects':{s:o['sha256'] for s,o in x['objects'].items()},'imports':{d:key(d) for d in x['imports']},'runtime':snapshot['runtime_files']})
  visiting.remove(n);return keys[n]
 for record in j(group+'/import-source-audit.json'):
  n=record['module']
  if n=='ExtractedDecoderPublicBinding':pd=prior['decoder-public-binding-20261016'];prefix=''
  else:
   assert n=='AspisR1PublicPreparation.Types';pd=prior['public-preparation-step-20261016'];prefix='proofs/'
  raw=pd[prefix+'successful-targets/'+n+'.json'];pr=json.loads(raw)
  assert sha(raw)==record['receipt_sha256'] and digest(pr['key'])==record['receipt_key_sha256']
  assert pr['exit_status']==0 and pr['axioms']['passed'] and pr['key']['runtime']==snapshot['runtime_files']
  assert pr['objects']==record['objects']==snapshot['modules'][n]['objects']
  assert pr['key']['source_sha256']==record['source_sha256']
  for ext,o in pr['objects'].items():assert sha(pd[prefix+'objects/'+n.replace('.','/')+ext])==o['sha256']
 for n,r in rs.items():
  count+=1;assert r==j(group+'/successful-targets/'+n+'.json')
  paths=[p for p in data if p.startswith(group+'/runs/') and p.endswith('/'+n+'/receipt.json')]
  assert len(paths)==1 and r==j(paths[0]);run=paths[0].removesuffix('/receipt.json')
  assert r['exit_status']==0 and r['axioms']['passed'] and r['limits']==limits
  assert r['key']['options']==['-j1','-M0'] and r['key']['runtime']==snapshot['runtime_files']
  assert r['process_swaps']==0 and r['cgroup_swap_current']=='0' and not r['dependency_build'] and not r['backend_build']
  source=data[group+'/sources/'+n.replace('.','/')+'.lean']
  assert source==data[run+'/source.lean']==(root/r['source_manifest_entry']['source']).read_bytes()
  assert sha(source)==r['key']['source_sha256']
  for ext,o in r['objects'].items():assert sha(data[group+'/objects/'+n.replace('.','/')+ext])==o['sha256']
  for dep,k in r['key']['imports'].items():
   if dep in rs:
    pr=rs[dep];assert k=={'receipt_key':digest(pr['key']),'objects':pr['objects']}
   else:assert k=={'closure_key':key(dep),'objects':snapshot['modules'][dep]['objects']}
  actual=[{'declaration':d,'axioms':[x.strip() for x in a.split(',') if x.strip()]} for d,a in re.findall(r"'([^']+)'\s+depends on axioms:\s*\[([^\]]*)\]",data[run+'/lean.log'].decode(),re.S)]
  assert actual==r['axioms']['reports'];reports.extend(actual)
assert count==7 and len(reports)==12
assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in reports)
assert data['proofs-naming-original/sources/PublicPreparationDiscriminantAudit.lean']==data['proofs-naming-adapted/sources/PublicPreparationDiscriminantAudit.lean']
failure=j('proofs-serializer/runs/joint-a/PreparationSerializerJoint/receipt.json')
assert failure==m['original_joint_failure'] and failure['exit_status']==1
assert 'instDiscriminantErrorIsize' in data['proofs-serializer/runs/joint-a/PreparationSerializerJoint/lean.log'].decode()
assert j('orchestration-stop.json')['not_a_lean_failure']
tool=root/'docs/research/100bit-spend-path-20261013/tools/public-preparation-discriminant-bridge.py'
spec=importlib.util.spec_from_file_location('adapter',tool);adapter=importlib.util.module_from_spec(spec);spec.loader.exec_module(adapter)
raw=subprocess.check_output(['git','-C',str(root),'show',m['producing_original_extension']+':docs/research/100bit-spend-path-20261013/lean/extracted-public-preparation-20261016/AspisR1PublicPreparation/Types.lean'])
adapted,items=adapter.adapt(raw);assert len(items)==5
assert adapted==data['proofs-naming-adapted/sources/AspisR1PublicPreparation/Types.lean']
old=prior['public-preparation-step-20261016']
assert data['proofs-naming-adapted/sources/AspisR1PublicPreparation/Funs.lean']==old['generated/AspisR1PublicPreparation/Funs.lean']
assert data['pack-naming.py']==(here/'pack.py').read_bytes()
assert data['run-naming.py']==(here/'run-naming.py').read_bytes()
assert data['continue-naming.py']==(here/'continue-naming.py').read_bytes()
print(f'PASS {len(data)} members; 7 green targets/12 standard reports; both28-tag checks; original joint failure and orchestration stop retained; old proof cache unchanged')
