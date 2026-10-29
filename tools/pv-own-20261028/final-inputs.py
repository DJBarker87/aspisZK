from pathlib import Path
import json,subprocess,hashlib,base64
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-own-20261028';D='/home/dombarker/project-offloads/codex-pv-own-20261028'
records=[json.loads(p.read_text())for p in E.glob('lean-*/receipt.json')]
assert sorted(r['attempt']for r in records)==list(range(61700,61800))
latest={}
for r in sorted(records,key=lambda r:r['attempt']):
 if r['exit']==0:latest[r['module']]=r
for r in latest.values():
 b=(R/r['source_path']).read_bytes();assert hashlib.sha256(b).hexdigest()==r['source_sha256'],r['module']
x=dict(projects={m:{k:r[k]for k in ['source_sha256','source_blob','source_revision','imports','dependency_objects']}for m,r in latest.items()},external=json.loads((R/'evidence/pv-world-20261028/external-object-manifest.json').read_text()))
b=json.dumps(x).encode();(E/'final-inputs.sha256').write_text(hashlib.sha256(b).hexdigest()+'\n')
script=(R/'tools/pv-own-20261028/fingerprint-cleanup.py').read_bytes()
code=f"from pathlib import Path\nimport base64\nD=Path({D!r})\n(D/'final-inputs.json').write_bytes(base64.b64decode({base64.b64encode(b).decode()!r}))\n(D/'fingerprint-cleanup.py').write_bytes(base64.b64decode({base64.b64encode(script).decode()!r}))\n"
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True);assert r.returncode==0
print('Prepared final private fingerprint of',len(latest),'project modules')
