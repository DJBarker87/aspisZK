from pathlib import Path
import subprocess,json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rows10-20261029';D='/home/dombarker/project-offloads/codex-pv-rows10-20261029'
manifest=(R/'evidence/pv-world-20261028/external-object-manifest.json').read_text()
code='''from pathlib import Path
import json,hashlib,subprocess,time
D=Path(DIR);old=Path('/home/dombarker/project-offloads/codex-pv-ownp-20261029')
e=json.loads((old/'env-J.json').read_text());roots=[Path(p)for p in e['LEAN_PATH'].split(':')];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=json.loads(MANIFEST)
for r in rows:
 p=next(p/(r['module']+'.olean') for p in roots if(p/(r['module']+'.olean')).exists())
 assert sha(p)==r['object_sha256'],r['module']
D.mkdir(exist_ok=True);(D/'lean-objects').mkdir(exist_ok=True);(D/'lean-sources/R1Z').mkdir(parents=True,exist_ok=True)
(D/'env-J.json').write_bytes((old/'env-J.json').read_bytes())
print(json.dumps(dict(ok=True,external_count=len(rows),environment_sha256=sha(D/'env-J.json'),toolchain=e['LEAN_GITHASH'],LEAN_PATH=e['LEAN_PATH'],checked_at=time.time(),project_imports=[],reuse='only pinned external objects; no project object imported')))
'''.replace('DIR',repr(D)).replace('MANIFEST',repr(manifest))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
j=json.loads(r.stdout);j['manifest_sha256']=hashlib.sha256(manifest.encode()).hexdigest();(E/'cohort-verification.json').write_text(json.dumps(j,indent=2)+'\n');print(j['external_count'])
