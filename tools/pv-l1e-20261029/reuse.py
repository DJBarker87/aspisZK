"""Verify h6 cache evidence read-only and stage the resolved L1 closure privately."""
from pathlib import Path
import json,subprocess,shlex
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l1e-20261029'
x=json.loads((E/'focused-resolution.json').read_text());sources=json.loads((E/'focused-project-sources.json').read_text());mods={m:v for m,v in x['resolved'].items() if 'imports' in v}
# Read-only receipt recovery: runjoin's live retained cache contains later
# completed objects than the committed index. Only exact selected source hashes
# and complete recorded fingerprints may be reused below.
recover=r'''import pathlib,json,sys
pins=json.load(sys.stdin);p=pathlib.Path('/home/dombarker/project-offloads/codex-pv-runjoin-20261026/runjoin32-lean/evidence');out={}
for f in sorted(p.glob('results-*.json')):
 for v in json.load(open(f)):
  m=v['module']
  if v.get('accepted') and m in pins and v['source_sha256']==pins[m]['sha256']:
   v['recovered_receipt_path']=str(f);out[m]=v
print(json.dumps(out))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(recover)],input=json.dumps(mods),text=True,capture_output=True)
assert r.returncode==0,r.stderr
(E/'recovered-runjoin-receipts.json').write_text(r.stdout)
records=json.loads(r.stdout)
reuse={m:records[m] for m in mods if m in records and records[m]['source_sha256']==mods[m]['sha256']}
external=json.loads((E/'external-authority.json').read_text())
code=r'''import sys,json,pathlib,hashlib
x=json.load(sys.stdin);p=pathlib.Path('/home/dombarker/project-offloads/codex-pv-l1e-20261029');old=pathlib.Path('/home/dombarker/project-offloads/codex-pv-runjoin-20261026/runjoin32-lean');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for d in ['objects','sources','external','evidence']:(p/d).mkdir(exist_ok=True)
checks=[];external={r['module'].replace('/','.'):r for r in x['external']}
for m,v in external.items():
 q=pathlib.Path(v['path']);assert sha(q)==v['object_sha256'],m
 dest=p/'external'/(m.replace('.','/')+'.olean');dest.parent.mkdir(parents=True,exist_ok=True)
 for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir','.so']:
  src=q.with_suffix(suffix);dst=dest.with_suffix(suffix)
  if src.is_file() and not dst.exists():dst.symlink_to(src)
for m,v in x['reuse'].items():
 rel=m.replace('.','/');s=old/'sources'/(rel+'.lean');o=old/'objects'/(rel+'.olean')
 assert sha(s)==x['mods'][m]['sha256']==v['source_sha256'],('source',m)
 assert sha(o)==v['object_sha256'],('object',m)
 ds=[]
 for d,r in v['dependencies'].items():
  expected=x['reuse'][d]['object_sha256'] if d in x['reuse'] else external[d]['object_sha256'] if d in external else None
  assert expected==r['sha256'],('fingerprint',m,d,expected,r)
  q=old/'objects'/(d.replace('.','/')+'.olean') if d in x['reuse'] else pathlib.Path(external[d]['path'])
  assert sha(q)==expected,('dependency-object',m,d)
  ds.append(dict(module=d,object_sha256=expected))
 checks.append(dict(module=m,source_sha256=sha(s),object_sha256=sha(o),dependencies=ds,receipt_attempt=v.get('attempt'),source_resolution=x['mods'][m]))
 dest=p/'objects'/(rel+'.olean');dest.parent.mkdir(parents=True,exist_ok=True)
 for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir']:
  src=o.with_suffix(suffix);dst=dest.with_suffix(suffix)
  if src.is_file() and not dst.exists():dst.symlink_to(src)
for m,s in x['sources'].items():
 q=p/'sources'/(m.replace('.','/')+'.lean');q.parent.mkdir(parents=True,exist_ok=True);q.write_text(s)
 assert sha(q)==x['mods'][m]['sha256']
env=json.load(open(old/'J.json'));base=json.load(open('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json'))
assert all(env[k]==base[k] for k in base if k!='LEAN_PATH'), 'toolchain mismatch'
original=env['LEAN_PATH'];env['LEAN_PATH']=str(p/'objects')+':'+str(p/'external');(p/'retry-J.json').write_text(json.dumps(env))
receipt=dict(all_match=True,reused=checks,toolchain={k:v for k,v in env.items() if k!='LEAN_PATH'},original_prefix=original,effective_prefix=env['LEAN_PATH'],prefix_note='Private read-only links retain identical selected project/external objects and complete dependency fingerprints; no extra project search path.',missing=sorted(set(x['mods'])-set(x['reuse'])))
(p/'evidence/reuse.json').write_text(json.dumps(receipt));print(json.dumps(receipt))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(dict(mods=mods,reuse=reuse,external=external,sources=sources)),text=True,capture_output=True)
(E/'reuse-transport.json').write_text(json.dumps(dict(exit=r.returncode,stderr=r.stderr)))
assert r.returncode==0,r.stderr
(E/'reuse.json').write_text(r.stdout)
r=json.loads(r.stdout);print('Verified',len(r['reused']),'project objects and all transitive fingerprints. Missing:',r['missing'])
