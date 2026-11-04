"""Retain verified current objects/sources; never delete the owned cache."""
from NFN_remote import *
import hashlib
C='/home/dombarker/project-offloads/codex-cx-slice-q-phase-cache-20261104'
latest={}
for line in (E/'NFN_ATTEMPTS.jsonl').read_text().splitlines():
 r=json.loads(line)
 if r['kind']=='lean':latest[r['module']]=r
selected=[]
for m,r in latest.items():
 if m=='NFN_PhaseInspect':continue
 assert r['exit_status']==0,(m,'failed latest object')
 p=E/(m+'.lean');assert hashlib.sha256(p.read_bytes()).hexdigest()==r['source_hashes']['NFN_generated/'+m+'.lean']
 selected.append(dict(module=m,source=p.read_text(),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),attempt=r['attempt']))
admit('NFN_EXPORT')
r=ssh('NFN_EXPORT','python3',f'''from pathlib import Path
import hashlib,json,shutil
b=Path({B!r});root=Path({C!r});export=root/'NFN_exports_20261104';export.mkdir(exist_ok=True);rows=[]
for x in json.loads({json.dumps(selected)!r}):
 m=x.pop('module');src=x.pop('source');stem=m.replace('.','/');p=export/(stem+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_text(src)
 assert hashlib.sha256(p.read_bytes()).hexdigest()==x['source_sha256']
 files=[]
 for suffix in ['.olean','.olean.private','.olean.server','.ir','.ilean']:
  before=b/'NFN_objects'/(stem+suffix)
  if before.is_file():
   after=export/(stem+suffix);shutil.copy2(before,after);files.append(dict(path=str(after),source_path=str(before),sha256=hashlib.sha256(after.read_bytes()).hexdigest(),bytes=after.stat().st_size))
 assert any(z['path'].endswith('.olean') for z in files)
 rows.append(dict(module=m,source_path=str(p),files=files,**x))
native=root/'NFN_native_20261104';native.mkdir(exist_ok=True);pins=[]
for p in (b/'NFN_native').iterdir():
 if not p.is_file():continue
 q=native/p.name;shutil.copy2(p,q);pins.append(dict(path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
print(json.dumps(dict(cache=str(root),export=str(export),objects=rows,native=pins,policy='COPIED and RETAINED; no workspace/cache/key deletion'),indent=1))
''');assert r.returncode==0,r.stderr
(E/'NFN_OBJECT_EXPORTS.json').write_text(r.stdout);print('exported',len(selected),'current objects')
rows=[json.loads(l) for l in (E/'NFN_ATTEMPTS.jsonl').read_text().splitlines()];paths=sorted({r['cgroup'] for r in rows if 'cgroup' in r})
r=ssh('NFN_SCOPE_AUDIT','python3',f'''from pathlib import Path
import json
active=[]
for n in {paths!r}:
 p=Path(n)/'cgroup.procs'
 if p.exists() and p.read_text().strip():active.append(dict(cgroup=n,pids=p.read_text().split()))
print(json.dumps(dict(recorded_scopes={len(paths)},active=active),indent=1))
''');assert r.returncode==0,r.stderr
assert json.loads(r.stdout)['active']==[];(E/'NFN_SCOPE_AUDIT.json').write_text(r.stdout)
