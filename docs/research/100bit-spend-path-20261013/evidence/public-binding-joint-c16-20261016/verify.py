#!/usr/bin/env python3
"""Read/hash current coherent universe, producing keys and retained interruptions."""
from pathlib import Path,PurePosixPath
import hashlib,importlib.util,inspect,json,re,tarfile
H=Path(__file__).resolve().parent;R=H.parents[4]
sha=lambda b:hashlib.sha256(b).hexdigest();digest=lambda x:sha(json.dumps(x,sort_keys=True).encode())
m=json.loads((H/'manifest.json').read_text());archive=H/m['archive'];assert sha(archive.read_bytes())==m['archive_sha256'] and archive.stat().st_size==m['archive_bytes']
with tarfile.open(archive) as t:
 members=t.getmembers();assert len(members)==m['archive_entries'] and len({x.name for x in members})==len(members)
 for x in members:
  p=PurePosixPath(x.name);assert not p.is_absolute() and '..' not in p.parts and (x.isfile() or x.islnk())
  if x.islnk():assert x.linkname in t.getnames()
 data={x.name:t.extractfile(x).read() for x in members}
entries={line.split('  ',1)[1]:line.split('  ',1)[0] for line in data['SHA256SUMS'].decode().splitlines()};assert set(entries)==set(data)-{'SHA256SUMS'}
for n,h in entries.items():assert sha(data[n])==h,n
j=lambda n:json.loads(data[n]);snapshot=j('external-inputs.json');finals=m['final_receipts'];assert len(finals)==8
excluded=j('excluded-old-universe.json');removed=set(excluded['removed_reverse_import_closure']);assert not removed&set(snapshot['modules'])
assert {'AspisR1PublicPreparation.Types','AspisR1PublicPreparation.Funs'}<=removed
assert not set(finals)&set(snapshot['modules'])
assert all(not set(x['imports'])&removed for x in snapshot['modules'].values())
keys={};visiting=set()
def key(n):
 if n in keys:return keys[n]
 assert n not in visiting;visiting.add(n);x=snapshot['modules'][n]
 keys[n]=digest({'source':x['source_sha256'],'objects':{s:o['sha256'] for s,o in x['objects'].items()},'imports':{d:key(d) for d in x['imports']},'runtime':snapshot['runtime_files']});visiting.remove(n);return keys[n]
count=0
for n,r in finals.items():
 assert r==j('successful-targets/'+n+'.json') and r['exit_status']==0 and r['axioms']['passed']
 assert r['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0'}
 assert r['process_swaps']==0 and r['cgroup_swap_current']=='0' and not r['dependency_build'] and not r['backend_build']
 assert r['key']['runtime']==snapshot['runtime_files'] and r['key']['options']==['-j1','-M0']
 name=n.replace('.','/');source=data['sources/'+name+'.lean']
 assert sha(source)==r['key']['source_sha256'] and source==(R/r['source_manifest_entry']['source']).read_bytes()
 matches=[p for p in data if p.startswith('runs/') and p.endswith('/'+n+'/receipt.json') and j(p)==r];assert len(matches)==1
 run=matches[0].rsplit('/',1)[0];assert data[run+'/source.lean']==source
 for suffix,o in r['objects'].items():assert sha(data['objects/'+name+suffix])==o['sha256']
 for dep,item in r['key']['imports'].items():
  if dep in finals:assert item=={'receipt_key':digest(finals[dep]['key']),'objects':finals[dep]['objects']}
  else:assert item=={'closure_key':key(dep),'objects':snapshot['modules'][dep]['objects']}
 reports=r['axioms']['reports'];count+=len(reports);assert len(reports)==r['source_manifest_entry']['axiom_requests']
 assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in reports)
 log=data[run+'/lean.log'].decode()
 for report in reports:assert report['declaration'] in log
assert count==19
# Recompute the unchanged-declaration inventory and the five-instance inverse.
def module(name,path):
 spec=importlib.util.spec_from_file_location(name,path);obj=importlib.util.module_from_spec(spec);spec.loader.exec_module(obj);return obj
B=R/'docs/research/100bit-spend-path-20261013'
b=module('bridge',B/'tools/public-binding-followup-kit/bridge-callers.py');pins=j('adapter-pins.json')
assert pins==json.loads((B/'lean/bridge-public-callers-c16-20261016/adapter-pins.json').read_text())
for name in ['Types.lean','Funs.lean']:
 raw=data['raw-current/'+name];prior=(B/'lean/extracted-public-preparation-20261016/AspisR1PublicPreparation'/name).read_bytes();p=pins['declarations'][name]
 assert sha(raw)==p['current_raw_sha256'] and sha(prior)==p['old_sha256']
 old=b.declarations(prior);new=b.declarations(raw)
 for item in p['unchanged_declarations']:
  n=item['declaration'];assert old[n]==new[n]
  assert sha(json.dumps(old[n],separators=(',',':')).encode())==item['token_sha256']
 assert sorted(set(new)-set(old))==p['new_declarations']
assert sum(len(x['unchanged_declarations']) for x in pins['declarations'].values())==79
raw=data['raw-current/Types.lean'];adapter=module('adapter',B/'tools/public-preparation-discriminant-bridge.py');adapter.expected=sha(raw)
code=inspect.getsource(adapter.adapt).replace(" and s.count('@[discriminant isize]')==0",'');exec(code,adapter.__dict__)
adapted,instances=adapter.adapt(raw)
assert adapted==data['sources/AspisR1PublicPreparation/Types.lean'] and instances==pins['instances']
assert data['raw-current/Funs.lean']==data['sources/AspisR1PublicPreparation/Funs.lean']
assert data['stage.py']==(B/'tools/public-binding-followup-kit/stage-joint-host.py').read_bytes()
assert data['resume-joint.py']==(B/'tools/public-binding-followup-kit/resume-joint-host.py').read_bytes()
assert data['pack.py']==(H/'pack.py').read_bytes()
for run in ['joint-b','joint-c']:
 r=j('runs/'+run+'/ExtractedPreparationSerializerWhole/receipt.json');assert r['exit_status']==-9 and not r['axioms']['passed'] and r['wall_seconds']<3
resume=j('resume-record.json');assert resume['attempts'][-1]['status']==0
assert all(x['full_snapshot_verified_once_in_memory'] and x['per_target_stat_identity_checks_retained'] for x in resume['attempts'])
print(f'PASS{len(members)} members;8 coherent current targets;19 standard-only reports;79 unchanged declarations; old-universe reverse imports excluded')
