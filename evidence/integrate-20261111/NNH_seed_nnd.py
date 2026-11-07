"""Import the retained NND module export, with exact per-file hashes."""
from pathlib import Path
import json,subprocess
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import hashlib,shutil,json
b=Path('/home/dombarker/project-offloads/codex-cx-integrate-20261111');s=Path('/home/dombarker/project-offloads/codex-cx-model-bridge-20261111/NND_objects');out=b/'NNH_seed';rows=[]
assert shutil.disk_usage(b).free>=40_000_000_000
for p in sorted(s.glob('NND_*')):
 if not p.is_file() or not any(str(p).endswith(z) for z in ['.olean','.olean.private','.olean.server','.ir']):continue
 q=out/p.name;h=hashlib.sha256(p.read_bytes()).hexdigest()
 if not q.exists():shutil.copy2(p,q)
 assert hashlib.sha256(q.read_bytes()).hexdigest()==h,str(q)
 rows.append(dict(path=str(p),destination=str(q),sha256=h,bytes=q.stat().st_size))
print(json.dumps(rows))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True);assert r.returncode==0,r.stderr
(E/'NNH_NND_IMPORTS.json').write_text(r.stdout);print('Imported',len(json.loads(r.stdout)),'objects')
