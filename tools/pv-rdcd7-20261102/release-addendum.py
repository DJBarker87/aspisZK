"""Read-only final audit object and launch fingerprint addendum; no replay."""
from pathlib import Path
import subprocess,json,hashlib,shlex
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd7-20261102';D='/home/dombarker/project-offloads/codex-pv-rdcd7-20261102';H='dombarker@100.108.41.90'
coh=json.load(open(E/'coherence-result.json'));pins={m:x['object_sha256'] for m,x in coh['modules'].items()};sources={m:x['source_sha256'] for m,x in coh['modules'].items()}
for n in [90797,90798,90799]:
 j=json.load(open(E/f'lean-{n}/receipt.json'));assert j['exit']==0
 d=json.load(open(E/j['dependencies_snapshot']))
 for m,x in d['objects'].items():
  if m in pins:assert pins[m]==x['object_sha256'],(n,m)
  pins[m]=x['object_sha256']
 assert hashlib.sha256((R/j['source_path']).read_bytes()).hexdigest()==j['source_sha256']
 sources[j['module']]=j['source_sha256']
code='''from pathlib import Path
import json,hashlib
D=Path(DIRECTORY);env=json.load(open(D/'env-J.json'));roots=[Path(x) for x in env['LEAN_PATH'].split(':')]
pins=PINS;sources=SOURCES
out={}
for m,h in pins.items():
 r=next(r for r in roots if (r/m.split('/')[0]).is_dir());p=r/(m+'.olean')
 assert hashlib.sha256(p.read_bytes()).hexdigest()==h,m
for m,h in sources.items():assert hashlib.sha256((D/'lean-sources'/(m+'.lean')).read_bytes()).hexdigest()==h,m
for m in ['R1Z/PV_RDCD5_V197Focused','R1Z/PV_RDCD5_V197FrozenManifest']:
 p=D/'lean-objects'/(m+'.olean');out[m]=dict(object_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size)
print(json.dumps(dict(status='PASS',new_release_objects=out,verified_existing_and_launch_objects=len(pins),verified_sources=len(sources))))
'''.replace('DIRECTORY',repr(D)).replace('PINS',repr(pins)).replace('SOURCES',repr(sources))
r=subprocess.run(['ssh',H,'python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
(E/'release-object-addendum.json').write_text(json.dumps(json.loads(r.stdout),indent=2)+'\n')
raw=E/'raw-audit';raw.mkdir(exist_ok=True)
subprocess.run(['scp','-q',H+':'+D+'/raw-audit/NEP_*_REACHABLE.txt',str(raw)+'/'],check=True)
qs=json.load(open(E/'consumer-audit-projection.json'))['queries'];files=list(raw.glob('*_REACHABLE.txt'));assert len(files)==len(qs),(len(files),len(qs))
manifest=[]
for p in files:
 b=p.read_bytes();item=dict(path=str(p.relative_to(E)),sha256=hashlib.sha256(b).hexdigest(),size=len(b))
 if len(b)>20*1024*1024:
  subprocess.run(['xz','-6',str(p)],check=True);p.with_suffix(p.suffix+'.sha256').write_text(item['sha256']+'\n');item['compressed']=str(p.relative_to(E))+'.xz'
 manifest.append(item)
(E/'raw-audit-files.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(r.stdout.strip());print('Collected',len(files),'raw reachable-constant inventories')
