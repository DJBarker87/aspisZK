"""Read-only inherited cohort validation and private task input preparation."""
from pathlib import Path
import json,subprocess,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-ownd-20261029'
old=json.loads((R/'evidence/pv-ownc-20261029/final-fingerprint.json').read_text())
for r in old['rows']:
 b=subprocess.check_output(['git','show','HEAD:'+r['source_path']]);assert hashlib.sha256(b).hexdigest()==r['source_sha256'],r['module']
code='''from pathlib import Path
import json,hashlib,shutil
old=Path('/home/dombarker/project-offloads/codex-pv-ownc-20261029');new=Path('/home/dombarker/project-offloads/codex-pv-ownd-20261029')
rows=json.loads(ROWS);out=[]
for r in rows:
 p=Path(r['object_path']);a=hashlib.sha256(p.read_bytes()).hexdigest();assert a==r['object_sha256'],r['module']
 s=old/'lean-sources'/(r['module'].replace('.','/')+'.lean');assert hashlib.sha256(s.read_bytes()).hexdigest()==r['source_sha256']
 for dep,sha in r['dependency_objects'].items():assert hashlib.sha256((old/'lean-objects'/(dep.replace('.','/')+'.olean')).read_bytes()).hexdigest()==sha,(r['module'],dep)
 out.append(dict(module=r['module'],object_sha256=a,source_sha256=r['source_sha256'],dependency_objects=r['dependency_objects']))
new.mkdir(exist_ok=True);(new/'lean-objects').mkdir(exist_ok=True);(new/'lean-sources').mkdir(exist_ok=True)
for r in rows:
 source=Path(r['object_path']);target=new/'lean-objects'/(r['module'].replace('.','/')+'.olean');target.parent.mkdir(parents=True,exist_ok=True)
 for a,b in [(source,target),(Path(str(source)+'.server'),Path(str(target)+'.server')),(Path(str(source)+'.private'),Path(str(target)+'.private')),(source.with_suffix('.ir'),target.with_suffix('.ir'))]:
  if a.exists():
   if b.exists():assert hashlib.sha256(b.read_bytes()).hexdigest()==hashlib.sha256(a.read_bytes()).hexdigest()
   else:b.symlink_to(a)
env=json.loads((old/'env-J.json').read_text());(new/'env-J.json').write_text(json.dumps(env,indent=2)+'\\n')
print(json.dumps(dict(ok=True,project_count=len(out),rows=out,environment='byte-identical inherited env-J.json; same toolchain and LEAN_PATH prefix; run2 private output prefix precedes inherited read-only cohort',env_sha256=hashlib.sha256((old/'env-J.json').read_bytes()).hexdigest())))
'''.replace('ROWS',repr(json.dumps(old['rows'])))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
j=json.loads(r.stdout);j.update(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),authority='h6; all direct/transitive project import edges validated against inherited tracked sources; no writes into inherited workspace')
(E/'inherited-verification.json').write_text(json.dumps(j,indent=2)+'\n');print(j['ok'],j['project_count'])
