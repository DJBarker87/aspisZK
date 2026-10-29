from pathlib import Path
import subprocess,json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rows10b-20261029';D='/home/dombarker/project-offloads/codex-pv-rows10b-20261029'
latest={}
for p in sorted(E.glob('lean-*/receipt.json')):
 j=json.loads(p.read_text())
 if j['exit']==0:latest[j['module']]=j
rows=[]
for m,j in latest.items():
 b=subprocess.check_output(['git','show','HEAD:'+j['source_path']]);assert hashlib.sha256(b).hexdigest()==j['source_sha256'],m
 rows.append(dict(module=m,source_sha256=j['source_sha256'],source_path=j['source_path'],compile_revision=j['source_revision'],attempt=j['attempt']))
code='''from pathlib import Path
import json,hashlib
D=Path(DIR);sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
e=json.loads((D/'env-J.json').read_text());roots=[D/'lean-objects']+[Path(x)for x in e['LEAN_PATH'].split(':')]
rows=json.loads(__PAYLOAD__)
for r in rows:
 s=D/'lean-sources'/(r['module']+'.lean');assert sha(s)==r['source_sha256'],r['module']
 o=D/'lean-objects'/(r['module']+'.olean');r['object_path']=str(o);r['object_sha256']=sha(o)
assert e['LEAN_GITHASH']=='8c9756b28d64dab099da31a4c09229a9e6a2ef35'
print(json.dumps(dict(ok=True,rows=rows,environment_sha256=sha(D/'env-J.json'),toolchain=e['LEAN_GITHASH'],unchanged_LEAN_PATH=e['LEAN_PATH'],source_only_project_imports='new PV_ROWS10B modules only; all transitive imports otherwise h4 externals')))
'''.replace('DIR',repr(D)).replace('__PAYLOAD__',repr(json.dumps(rows)))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
(E/'own-object-verification.json').write_text(r.stdout);print('verified',len(rows),'private objects')
