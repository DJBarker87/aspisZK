#!/usr/bin/env python3
"""Read/hash-only evidence checks. No compiler or archive extraction."""
from pathlib import Path, PurePosixPath
import hashlib,json,re,tarfile
here=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
digest=lambda x:sha(json.dumps(x,sort_keys=True).encode())
m=json.loads((here/'manifest.json').read_text())
archive=here/m['archive']
assert sha(archive.read_bytes())==m['archive_sha256']
assert archive.stat().st_size==m['archive_bytes']
with tarfile.open(archive,'r:gz') as t:
 members=t.getmembers();assert len(members)==m['archive_entries']
 assert len({x.name for x in members})==len(members)
 for x in members:
  p=PurePosixPath(x.name);assert not p.is_absolute() and '..' not in p.parts
  assert x.isfile() or x.islnk(),x.name
  if x.islnk():assert x.linkname in t.getnames()
 data={x.name:t.extractfile(x).read() for x in members}
entries={line.split('  ',1)[1]:line.split('  ',1)[0] for line in data['SHA256SUMS'].decode().splitlines()}
assert set(entries)==set(data)-{'SHA256SUMS'}
for name,h in entries.items():assert sha(data[name])==h,name
j=lambda name:json.loads(data[name])
n=m['module'];r=j('successful-targets/'+n+'.json')
assert r==m['receipt']==j('runs/proof-b/'+n+'/receipt.json')
assert r['exit_status']==0 and r['axioms']['passed']
assert r['key']['options']==['-j1','-M0']
assert r['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0'}
assert r['process_swaps']==0 and r['cgroup_swap_current']=='0'
assert not r['dependency_build'] and not r['backend_build']
source=data['sources/'+n+'.lean']
assert source==data['runs/proof-b/'+n+'/source.lean']
assert source==(here.parents[4]/r['source_manifest_entry']['source']).read_bytes()
assert sha(source)==r['key']['source_sha256']
assert sha(data['objects/'+n+'.olean'])==r['objects']['.olean']['sha256']
reports=[{'declaration':name,'axioms':[x.strip() for x in ax.split(',') if x.strip()]}
 for name,ax in re.findall(r"'([^']+)'\s+depends on axioms:\s*\[([^\]]*)\]",data['runs/proof-b/'+n+'/lean.log'].decode(),re.S)]
assert reports==r['axioms']['reports'] and len(reports)==5
assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in reports)
snapshot=j('external-inputs-proof.json')
assert snapshot==j('runs/proof-b/external-inputs.json')
assert r['key']['runtime']==snapshot['runtime_files']
keys={};visiting=set()
def key(name):
 if name in keys:return keys[name]
 assert name not in visiting;visiting.add(name);x=snapshot['modules'][name]
 keys[name]=digest({'source':x['source_sha256'],'objects':{s:o['sha256'] for s,o in x['objects'].items()},'imports':{d:key(d) for d in x['imports']},'runtime':snapshot['runtime_files']})
 visiting.remove(name);return keys[name]
for name,item in r['key']['imports'].items():
 assert item=={'closure_key':key(name),'objects':snapshot['modules'][name]['objects']}
# Verify the exact two producing receipts/artifacts and their complete import keys.
base=j('input-manifests/base-snapshot.json');basekeys={}
def basekey(name):
 if name in basekeys:return basekeys[name]
 x=base['modules'][name]
 basekeys[name]=digest({'source':x['source_sha256'],'objects':{s:o['sha256'] for s,o in x['objects'].items()},'imports':{d:basekey(d) for d in x['imports']},'runtime':base['runtime_files']})
 return basekeys[name]
audit=j('import-source-audit.json');assert [a['module'] for a in audit]==['AspisR1PublicPreparation.Types','AspisR1PublicPreparation.Funs']
prior={}
for a in audit:
 name=a['module'];prefix='imports/'+name.replace('.','/')+'/'
 raw=data[prefix+'receipt.json'];pr=json.loads(raw);prior[name]=pr
 assert sha(raw)==a['receipt_sha256'] and digest(pr['key'])==a['receipt_key_sha256']
 assert pr['exit_status']==0 and pr['axioms']['passed'] and pr['key']['runtime']==snapshot['runtime_files']
 assert pr['objects']==a['objects']==snapshot['modules'][name]['objects']
 source=data[prefix+'source.lean'];assert sha(source)==a['source_sha256']==pr['key']['source_sha256']
 # Current bridge overlay comes from C's independently checked naming adapter.
 assert source==(here.parents[4]/pr['source_manifest_entry']['source']).read_bytes()
 for suffix,obj in pr['objects'].items():assert sha(data[prefix+'object'+suffix])==obj['sha256']
 for dep,item in pr['key']['imports'].items():
  if dep in prior:assert item=={'receipt_key':digest(prior[dep]['key']),'objects':prior[dep]['objects']}
  else:assert item=={'closure_key':basekey(dep),'objects':base['modules'][dep]['objects']}
# Bind retained imports to C's archived, independently audited naming gate.
prior_dir=here.parent/'public-preparation-naming-20261016'
pm=json.loads((prior_dir/'manifest.json').read_text());pa=prior_dir/pm['archive']
assert sha(pa.read_bytes())==pm['archive_sha256']=='b634c0cd24a1b258d7c269cfbc0c1605a2cdd8833558b9dd334ef13ed503bc05'
with tarfile.open(pa,'r:gz') as pt:
 for name in prior:
  prefix='imports/'+name.replace('.','/')+'/'
  assert data[prefix+'receipt.json']==pt.extractfile('proofs-naming-adapted/successful-targets/'+name+'.json').read()
  assert data[prefix+'source.lean']==pt.extractfile('proofs-naming-adapted/sources/'+name.replace('.','/')+'.lean').read()
assert a['module']=='AspisR1PublicPreparation.Funs'
mirror=here.parents[4]/'docs/research/100bit-spend-path-20261013/lean/extracted-public-preparation-20261016/AspisR1PublicPreparation/Funs.lean'
assert data['imports/AspisR1PublicPreparation/Funs/source.lean']==mirror.read_bytes()
failed=j('runs/proof-a/'+n+'/receipt.json')
assert failed['exit_status']==1 and not failed['axioms']['passed']
assert 'sorryAx' in data['runs/proof-a/'+n+'/lean.log'].decode()
assert '(↑row + ↑1#u8)' in data['runs/proof-a/'+n+'/lean.log'].decode()
assert sha(data['runs/proof-a/'+n+'/source.lean'])==failed['key']['source_sha256']
assert data['stage.py']==(here/'stage.py').read_bytes()
assert data['pack.py']==(here/'pack.py').read_bytes()
print(f'PASS {len(members)} archive members; 2 adapted generated receipts/objects; 5 standard-only reports; first failed receipt retained; constructor/step carry proved, full33/runtime OPEN')
