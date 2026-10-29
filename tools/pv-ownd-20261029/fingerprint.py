"""Read-only coherent inherited/new source and object/import freeze."""
from pathlib import Path
import json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-ownd-20261029';D='/home/dombarker/project-offloads/codex-pv-ownd-20261029'
inherited=json.loads((E/'inherited-verification.json').read_text())['rows'];rows={r['module']:r for r in inherited};spec=[]
for p in E.glob('lean-*/receipt.json'):
 j=json.loads(p.read_text())
 if j['exit']==0:
  m=j['module'].replace('/','.');b=(R/j['source_path']).read_bytes();assert hashlib.sha256(b).hexdigest()==j['source_sha256'],m
  assert b==subprocess.check_output(['git','show','HEAD:'+j['source_path']]),m
  r=dict(module=m,source_path=j['source_path'],source_sha256=j['source_sha256'],source_blob=j['source_blob'],dependency_objects=j['dependency_objects'],attempt=j['attempt'])
  rows[m]=r;spec.append(r)
code='''from pathlib import Path
import json,hashlib
D=Path(DIR);rows=json.loads(ROWS);new=json.loads(NEW);out=[]
old=Path('/home/dombarker/project-offloads/codex-pv-ownc-20261029')
assert (D/'env-J.json').read_bytes()==(old/'env-J.json').read_bytes(), 'inherited environment bytes'
env_sha=hashlib.sha256((D/'env-J.json').read_bytes()).hexdigest()
for m,r in rows.items():
 p=D/'lean-objects'/(m.replace('.','/')+'.olean');sha=hashlib.sha256(p.read_bytes()).hexdigest()
 if 'object_sha256' in r:assert sha==r['object_sha256'],m
 for dep,expected in r['dependency_objects'].items():
  q=D/'lean-objects'/(dep.replace('.','/')+'.olean');assert hashlib.sha256(q.read_bytes()).hexdigest()==expected,(m,dep)
  assert dep in rows,dep
 if m in new:
  s=D/'lean-sources'/(m.replace('.','/')+'.lean');assert hashlib.sha256(s.read_bytes()).hexdigest()==r['source_sha256'],m
 out.append(dict(**r,selected_object=str(p),selected_sha256=sha))
print(json.dumps(dict(ok=True,project_count=len(rows),new_count=len(new),identical_inherited_environment=True,env_sha256=env_sha,rows=out)))
'''.replace('DIR',repr(D)).replace('ROWS',repr(json.dumps(rows))).replace('NEW',repr(json.dumps([r['module'] for r in spec])))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
j=json.loads(r.stdout);j['source_revision']=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();j['scope']='all new and inherited source-pinned project objects, every direct/transitive project edge; inherited env-J unchanged; external cohort checked separately'
(E/'final-fingerprint.json').write_text(json.dumps(j,indent=2)+'\n');print(j['ok'],j['new_count'],j['project_count'])
