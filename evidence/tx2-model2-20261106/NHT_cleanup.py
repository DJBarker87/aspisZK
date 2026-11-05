"""Hash-verify retained exports before deleting only owned rebuildable outputs."""
from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
export=json.loads((E/'NHT_EXPORT.json').read_text())
binary={n:json.loads((E/'NHT_L067'/(n+'_BINARY_PIN.json')).read_text()) for n in ['NHT_Driver','NHT_ProofDriver']}
code='''from pathlib import Path
import json,hashlib
b=Path('/home/dombarker/project-offloads/codex-cx-tx2-model2-20261106')
export=json.loads(INPUT_EXPORT)
binaries=json.loads(INPUT_BINARIES)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
removed=[]
for r in export['own_exports']:
 p=Path(r['source']);q=Path(r['destination'])
 assert p.is_relative_to(b/'NHT_objects') and q.is_file() and sha(q)==r['sha256']
 assert p.is_file() and sha(p)==r['sha256']
 removed.append(dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size));p.unlink()
for n,r in binaries.items():
 p=b/'NHT_native'/n;assert sha(p)==r['sha256']
 removed.append(dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size));p.unlink()
 for q in [p.with_suffix('.c'),p.with_suffix('.o')]:
  if q.is_file():removed.append(dict(path=str(q),sha256=sha(q),bytes=q.stat().st_size));q.unlink()
assert Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NHT_exports_20261106').is_dir()
print(json.dumps(dict(removed=removed,removed_bytes=sum(r['bytes'] for r in removed),cache_retained=True,no_prover_submitted=True)))
'''.replace('INPUT_EXPORT',repr(json.dumps(export))).replace('INPUT_BINARIES',repr(json.dumps(binary)))
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
assert r.returncode==0,r.stderr
(E/'NHT_HOST_END.json').write_text(r.stdout);print(r.stdout)
