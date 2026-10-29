from pathlib import Path
import json,hashlib,subprocess,lzma
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-owno-20261029'
D='/home/dombarker/project-offloads/codex-pv-owno-20261029'
old=json.loads((R/'evidence/pv-ownc-20261029/final-fingerprint.json').read_text())
for r in old['rows']:
 b=(R/r['source_path']).read_bytes();assert hashlib.sha256(b).hexdigest()==r['source_sha256']
manifest=(R/'evidence/pv-world-20261028/external-object-manifest.json').read_text()
code='''from pathlib import Path
import json,hashlib,time
D=Path(DIR);old=Path('/home/dombarker/project-offloads/codex-pv-ownc-20261029')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
e=json.loads((old/'env-J.json').read_text());roots=[old/'lean-objects']+[Path(p) for p in e['LEAN_PATH'].split(':')]
rows=json.loads(ROWS)
for r in rows:
 p=Path(r['object_path']);assert sha(p)==r['object_sha256'],r['module']
 s=old/'lean-sources'/(r['module'].replace('.','/')+'.lean');assert sha(s)==r['source_sha256'],r['module']
 for dep,h in r['dependency_objects'].items():
  p=next(p/(dep.replace('.','/')+'.olean') for p in roots if (p/(dep.replace('.','/')+'.olean')).exists());assert sha(p)==h,(r['module'],dep)
external=json.loads(MANIFEST)
for r in external:
 p=next(p/(r['module']+'.olean') for p in roots if (p/(r['module']+'.olean')).exists());assert sha(p)==r['object_sha256'],r['module']
D.mkdir(exist_ok=True);(D/'lean-objects/R1Z').mkdir(parents=True,exist_ok=True);(D/'lean-sources/R1Z').mkdir(parents=True,exist_ok=True)
# Copy verified objects only; no write into inherited cache. Keep same env prefix.
import shutil
for r in rows:
 dest=D/'lean-objects'/(r['module'].replace('.','/')+'.olean');dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(r['object_path'],dest)
(D/'env-J.json').write_bytes((old/'env-J.json').read_bytes())
print(json.dumps(dict(ok=True,project_count=len(rows),external_count=len(external),env_sha256=sha(D/'env-J.json'),toolchain_and_LEAN_PATH_prefix='identical to ownc; verified copies in private prefix',checked_at=time.time())))
'''.replace('DIR',repr(D)).replace('ROWS',repr(json.dumps(old['rows']))).replace('MANIFEST',repr(manifest))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
j=json.loads(r.stdout);j.update(authority='h6; ownc final-fingerprint recorded source/object/transitive import identities, h4 external manifest',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),inherited_fingerprint_sha256=hashlib.sha256((R/'evidence/pv-ownc-20261029/final-fingerprint.json').read_bytes()).hexdigest())
(E/'cohort-verification.json').write_text(json.dumps(j,indent=2)+'\n');print(j)
