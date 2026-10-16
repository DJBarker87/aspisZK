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
assert r==m['receipt']==j('runs/binding-a/'+n+'/receipt.json')
assert r['exit_status']==0 and r['axioms']['passed']
assert r['key']['options']==['-j1','-M0']
assert r['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0'}
assert r['process_swaps']==0 and r['cgroup_swap_current']=='0'
assert not r['dependency_build'] and not r['backend_build']
source=data['sources/'+n+'.lean']
assert source==data['runs/binding-a/'+n+'/source.lean']
assert source==(here.parents[4]/r['source_manifest_entry']['source']).read_bytes()
assert sha(source)==r['key']['source_sha256']
assert sha(data['objects/'+n+'.olean'])==r['objects']['.olean']['sha256']
reports=[{'declaration':name,'axioms':[x.strip() for x in ax.split(',') if x.strip()]}
 for name,ax in re.findall(r"'([^']+)'\s+depends on axioms:\s*\[([^\]]*)\]",data['runs/binding-a/'+n+'/lean.log'].decode(),re.S)]
assert reports==r['axioms']['reports'] and len(reports)==7
assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in reports)
snapshot=j('external-inputs-binding.json')
assert snapshot==j('runs/binding-a/external-inputs.json')
assert r['key']['runtime']==snapshot['runtime_files']
keys={};visiting=set()
def key(name):
 if name in keys:return keys[name]
 assert name not in visiting;visiting.add(name);x=snapshot['modules'][name]
 keys[name]=digest({'source':x['source_sha256'],'objects':{s:o['sha256'] for s,o in x['objects'].items()},'imports':{d:key(d) for d in x['imports']},'runtime':snapshot['runtime_files']})
 visiting.remove(name);return keys[name]
for name,item in r['key']['imports'].items():
 assert item=={'closure_key':key(name),'objects':snapshot['modules'][name]['objects']}
prior=here.parent/'decoder-public-bridge-20261016'
pm=json.loads((prior/'manifest.json').read_text());pa=prior/pm['archive']
assert sha(pa.read_bytes())==pm['archive_sha256']
audit=j('import-source-audit.json');assert len(audit)==7
with tarfile.open(pa,'r:gz') as pt:
 for a in audit:
  name=a['module'];raw=pt.extractfile('caller-adapted/successful-targets/'+name+'.json').read()
  assert sha(raw)==a['receipt_sha256'];pr=json.loads(raw)
  assert pr['exit_status']==0 and pr['axioms']['passed']
  assert digest(pr['key'])==a['receipt_key_sha256']
  assert pr['key']['source_sha256']==a['source_sha256']
  assert pr['objects']==a['objects']==snapshot['modules'][name]['objects']
  assert pr['key']['runtime']==snapshot['runtime_files']
  ps=pt.extractfile('caller-adapted/sources/'+name.replace('.','/')+'.lean').read()
  assert sha(ps)==a['source_sha256']
  for suffix,obj in a['objects'].items():
   assert sha(pt.extractfile('caller-adapted/objects/'+name.replace('.','/')+suffix).read())==obj['sha256']
assert data['stage.py']==(here/'stage.py').read_bytes()
assert data['pack.py']==(here/'pack.py').read_bytes()
print(f'PASS {len(members)} archive members; 7 exact predecessor receipts/objects; 7 standard-only reports; fixed both-variant carrier, caller hd/hs OPEN')
