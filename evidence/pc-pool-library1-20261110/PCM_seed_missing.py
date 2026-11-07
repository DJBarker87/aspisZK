"""Recover selected missing dependencies from a retained export's pinned baseline."""
from pathlib import Path
import json,lzma,hashlib,subprocess,sys
E=Path(__file__).resolve().parent
p=E.parent/'pc-deposit-children1-20261110/PCF_IMPORTS.json.xz'
ex=json.loads((E.parent/'pc-deposit-children1-20261110/PCF_EXPORT.json').read_text())
assert hashlib.sha256(p.read_bytes()).hexdigest()==ex['seed_manifest_sha256']
manifest=json.loads(lzma.open(p).read());rows=[]
for module in sys.argv[1:]:
 for rel,r in manifest.items():
  if rel==module.replace('.','/')+'.olean' or rel.startswith(module.replace('.','/')+'.olean.'):
   assert 'codex-cx-tx2-entry5' not in r['source']
   rows.append(dict(source=r['source'],relative=rel,sha256=r['sha256']))
 assert any(r['relative']==module.replace('.','/')+'.olean' for r in rows),module
B='/home/dombarker/project-offloads/codex-pc-pool-library1-cache-20261110'
code='''from pathlib import Path
import json,hashlib,shutil
b=Path(B);out=[]
for r in rows:
 p=Path(r['source']);q=b/'PCM_dependencies'/r['relative'];q.parent.mkdir(parents=True,exist_ok=True)
 assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256']
 if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==r['sha256']
 else:shutil.copy2(p,q)
 out.append(dict(r,destination=str(q),bytes=q.stat().st_size))
print(json.dumps(out))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input='B='+repr(B)+'\nrows='+repr(rows)+'\n'+code,text=True,capture_output=True);assert r.returncode==0,r.stderr
with (E/'PCM_MISSING_IMPORTS.jsonl').open('a') as f:
 for row in json.loads(r.stdout):f.write(json.dumps(row)+'\n')
print('PCM missing dependency copies:',len(rows))
