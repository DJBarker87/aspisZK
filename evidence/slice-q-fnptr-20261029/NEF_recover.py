from NEF_host import *
r=py(f'''from pathlib import Path
import json
b=Path({B!r});names=[str(p.relative_to(b)) for p in (b/'NEF_extracted').rglob('*.lean')]+['NEF_FROZEN_EXTRACTION_PINS.json']+[str(p.relative_to(b)) for p in b.glob('NEF_K*-artifacts.json')]
print(json.dumps({{n:(b/n).read_text() for n in names if (b/n).is_file()}}))
''');assert r.returncode==0,r.stderr
for n,t in json.loads(r.stdout).items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
