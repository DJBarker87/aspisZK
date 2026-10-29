"""Read-only source/object/import fingerprint; no rebuild or substitution."""
from pathlib import Path
import json,subprocess,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-ownb-20261029';D='/home/dombarker/project-offloads/codex-pv-ownb-20261029'
rows={}
for p in sorted(E.glob('lean-*/receipt.json')):
 j=json.loads(p.read_text())
 if j['exit']==0:rows[j['module'].replace('/','.')]=j
spec=[]
for m,j in rows.items():
 p=R/j['source_path'];b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==j['source_sha256'],m
 spec.append(dict(module=m,source_path=j['source_path'],source_sha256=j['source_sha256'],dependency_objects=j['dependency_objects'],imports=j['imports'],attempt=j['attempt']))
code='''from pathlib import Path
import json,hashlib
D=Path(DIR);rows=json.loads(SPEC);out=[]
for r in rows:
 s=D/'lean-sources'/(r['module'].replace('.','/')+'.lean');assert hashlib.sha256(s.read_bytes()).hexdigest()==r['source_sha256'],r['module']
 p=D/'lean-objects'/(r['module'].replace('.','/')+'.olean');actual=hashlib.sha256(p.read_bytes()).hexdigest()
 for dep,sha in r['dependency_objects'].items():
  q=D/'lean-objects'/(dep.replace('.','/')+'.olean');assert hashlib.sha256(q.read_bytes()).hexdigest()==sha,(r['module'],dep)
 for dep in r['imports']:
  if dep.startswith('R1Z.'):assert dep in {x['module'] for x in rows},dep
 out.append(dict(**r,object_path=str(p),object_sha256=actual))
print(json.dumps(dict(ok=True,project_count=len(out),rows=out)))
'''.replace('DIR',repr(D)).replace('SPEC',repr(json.dumps(spec)))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
j=json.loads(r.stdout);j['source_revision']=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();j['scope']='all successful private project modules, every direct/transitive project edge checked; no h6 reuse; external cohort separately checked'
(E/'final-fingerprint.json').write_text(json.dumps(j,indent=2)+'\n');print(j['ok'],j['project_count'])
