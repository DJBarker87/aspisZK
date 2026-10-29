from pathlib import Path
import json,hashlib,re,os
B=Path('/home/dombarker/project-offloads');D=B/'codex-pv-mfb-20261029';D.mkdir(exist_ok=True)
req=json.load(open(D/'request.json'));sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
envs=[]
for job in sorted(B.glob('codex-pv-*')):
 for ep in job.glob('*env*.json'):
  try:e=json.load(open(ep))
  except Exception:continue
  if isinstance(e,dict) and 'LEAN_PATH'in e and 'LEAN'in e:envs.append((job,ep,e))
results=[]
for row in req:
 cs=row['closing'];m=cs['module'].replace('.','/');found=[]
 for job,ep,e in envs:
  roots=[job/'lean-objects']+[Path(x) for x in e['LEAN_PATH'].split(':')]
  ob=next((p/(m+'.olean') for p in roots if (p/(m+'.olean')).exists()),None)
  if ob is None or job not in ob.parents:continue
  ss=[job/x/(m+'.lean') for x in ['lean-sources','lean','sources']]
  sp=next((p for p in ss if p.exists()),None)
  found.append(dict(job=str(job),env_path=str(ep),object_path=str(ob),source_path=str(sp) if sp else None,source_sha256=sha(sp) if sp else None,source_matches_closing=bool(sp and sha(sp)==cs['sha256'])))
 results.append(dict(id=row['id'],closing=cs,cohorts=found))
(D/'inventory.json').write_text(json.dumps(results,indent=2));print([(r['id'],[(Path(x['job']).name,x['source_matches_closing']) for x in r['cohorts']]) for r in results])
