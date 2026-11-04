from pathlib import Path
import subprocess,json,lzma,hashlib
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-slice-s-retarget3-20261104'
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=f'''from pathlib import Path
import json,base64
b=Path({B!r});print(json.dumps({{n:base64.b64encode((b/n).read_bytes()).decode() for n in ['NGF_CACHE_IMPORTS.json.xz','NGF_CACHE_IMPORTS.json.sha256','NGF_SEED_RESERVATION.log','NGF_SEED_RESERVATION.json']}}))
''',text=True,capture_output=True);assert r.returncode==0,r.stderr
import base64
for n,v in json.loads(r.stdout).items():(E/n).write_bytes(base64.b64decode(v))
raw=lzma.decompress((E/'NGF_CACHE_IMPORTS.json.xz').read_bytes());assert hashlib.sha256(raw).hexdigest()==(E/'NGF_CACHE_IMPORTS.json.sha256').read_text().strip()
x=json.loads(raw);by={p['source']:p for p in x['selected']};exp=json.loads((E.parent/'slice-s-retarget-20261104/NFY_EXPORT.json').read_text())
for p in exp['exports']:assert by[p['path']]['sha256']==p['sha256'],p
(E/'NGF_SEED_CHECK.json').write_text(json.dumps(dict(status='PASS',files=len(by),bytes=x['bytes'],unique_bytes=x['unique_bytes'],NFY_exports_checked=len(exp['exports']),manifest_sha256=hashlib.sha256(raw).hexdigest()),indent=1)+'\n')
print((E/'NGF_SEED_CHECK.json').read_text())
