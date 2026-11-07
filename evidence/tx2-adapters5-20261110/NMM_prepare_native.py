from NMM_transport import *
admission('NMM_P002',scope=False)
r=ssh('python3',f'''from pathlib import Path
import shutil,hashlib,json
b=Path({B!r});s=Path('/home/dombarker/project-offloads/codex-cx-tx2-adapters4-20261110/NLK_src');d=b/'NMM_src'
assert not d.exists()
shutil.copytree(s,d)
pins=[dict(path=str(p.relative_to(d)),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in sorted(d.rglob('*')) if p.is_file()]
print(json.dumps(dict(source=str(s),destination=str(d),bytes=sum(p['bytes'] for p in pins),pins=pins)))
''');assert r.returncode==0,r.stderr
(E/'NMM_NATIVE_SEED.json').write_text(r.stdout)
print('Native source seed copied and hashed')
