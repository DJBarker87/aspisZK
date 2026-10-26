"""Read-only integrity audit of authorized recovery roots; never compile."""
from pathlib import Path
import subprocess,json,shlex
O=Path(__file__).parent
remote='''from pathlib import Path
import json,hashlib,collections
B=Path('/home/dombarker/project-offloads');T=B/'aspis-fs-generic-20261006/evidence';J=B/'aspis-joint-20261019';U=B/'codex-cx-import-union-20261022'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
rows=json.loads((T/'EJR_all-restored-sources.json').read_text())
profiles={p.name:json.loads(p.read_text()) for p in T.glob('EJS_*-sources.json')}
for rs in profiles.values():rows.extend(rs)
for r in json.loads((T/'EJR_library-source-provenance.json').read_text()):
 rows.append(dict(r,host_path=str(U/'sources'/(r['module']+'.lean'))))
sources=[]
for r in rows:
 p=Path(r['host_path']);actual=sha(p) if p.is_file() else None
 if actual!=r['source_sha256']:sources.append(dict(path=str(p),expected=r['source_sha256'],actual=actual))
a=[json.loads(l) for l in (T/'EJR_attempts.jsonl').read_text().splitlines()];latest={r['key']:r for r in a};roots={'joint':J,'union':U,'library':U/'retained-objects'}
for rs in profiles.values():
 for r in rs:
  if r['workspace'] not in ('joint','union'):roots[r['workspace']]=U/r['workspace']
objects=[];checked=0
for k,r in latest.items():
 if r['exit']!=0 or not r.get('object_sha256') or r['workspace'] not in roots:continue
 root=roots[r['workspace']];p=(root if r['workspace']=='library' else root/'objects')/(r['module']+'.olean');actual=sha(p) if p.is_file() else None;checked+=1
 if actual!=r['object_sha256']:objects.append(dict(key=k,path=str(p),expected=r['object_sha256'],actual=actual,attempt=r['attempt']))
reuses=[json.loads(l) for l in (T/'EJR_reuses.jsonl').read_text().splitlines()];reuse_bad=[];reused_checked=0
for k,r in {r['key']:r for r in reuses}.items():
 if k in latest and latest[k]['exit']==0:continue
 p=Path(r['target']);actual=sha(p) if p.is_file() else None;reused_checked+=1
 if actual!=r['object_sha256']:reuse_bad.append(dict(key=k,path=str(p),recorded_source=r['source'],expected=r['object_sha256'],actual=actual))
pins={str(p):dict(sha256=sha(p),bytes=p.stat().st_size) for p in [T/'EJR_build_host.py',T/'run2.py',B/'r1-privacy-build-integration-20261019/tools/run-joint.sh',B/'r1-privacy-build-integration-20261019/env/J.json']}
print(json.dumps(dict(source_entries_checked=len(rows),source_mismatches=sources,latest_success_objects_checked=checked,latest_success_object_mismatches=objects,reused_objects_checked=reused_checked,reused_object_mismatches=reuse_bad,infrastructure_pins=pins,rule='Read-only snapshot. A hash match is artifact integrity, not a release or transitive security proof. Legacy and superseded profile failures remain excluded.')))
'''
d=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(remote)],text=True));(O/'EJS_integrity.json').write_text(json.dumps(d,indent=2)+'\n');print(json.dumps({k:v for k,v in d.items() if k.endswith('_checked')}));print('mismatches',len(d['source_mismatches']),len(d['latest_success_object_mismatches']),len(d['reused_object_mismatches']))
