"""Final read-only source, selected-object and transitive import verification."""
from pathlib import Path
import json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-ownk-20261029';D='/home/dombarker/project-offloads/codex-pv-ownk-20261029'
rows={}
for p in sorted(E.glob('lean-*/receipt.json')):
 j=json.loads(p.read_text())
 if j['exit']==0:
  b=subprocess.check_output(['git','show','HEAD:'+j['source_path']]);assert hashlib.sha256(b).hexdigest()==j['source_sha256'],j['module']
  rows[j['module']]=j
old=json.loads((R/'evidence/pv-ownc-20261029/final-fingerprint.json').read_text())['rows']
external=json.loads((R/'evidence/pv-world-20261028/external-object-manifest.json').read_text())
code='''from pathlib import Path
import hashlib,json,time
D=Path(DIR);env=json.loads((D/'env-J.json').read_text());roots=[D/'lean-objects']+[Path(x)for x in env['LEAN_PATH'].split(':')]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def select(m):
 rel=m.replace('.','/')+'.olean'
 return next(p/rel for p in roots if(p/rel).exists())
rows=json.loads(ROWS);old=json.loads(OLD);ext=json.loads(EXT);out=[]
for r in ext:assert sha(select(r['module']))==r['object_sha256'],r['module']
for r in old:
 m=r['module'];assert sha(select(m))==r['object_sha256'],m
 for d,h in r['dependency_objects'].items():assert sha(select(d))==h,(m,d)
for r in rows:
 m=r['module'];s=D/'lean-sources'/(m+'.lean');assert sha(s)==r['source_sha256'],m
 for d,h in r['dependency_objects'].items():assert sha(select(d))==h,(m,d)
 out.append(dict(module=m,source_path=r['source_path'],source_sha256=r['source_sha256'],source_blob=r['source_blob'],object_path=str(select(m)),object_sha256=sha(select(m)),dependency_objects=r['dependency_objects']))
print(json.dumps(dict(ok=True,checked_at=time.time(),external_count=len(ext),inherited_project_count=len(old),private_project_count=len(rows),all_recorded_direct_and_transitive_imports_checked=True,rows=out)))
'''.replace('DIR',repr(D)).replace('ROWS',repr(json.dumps(list(rows.values())))).replace('OLD',repr(json.dumps(old))).replace('EXT',repr(json.dumps(external)))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
j=json.loads(r.stdout);j['source_revision']=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();(E/'final-fingerprint.json').write_text(json.dumps(j,indent=2)+'\n');print({k:v for k,v in j.items()if k!='rows'})
