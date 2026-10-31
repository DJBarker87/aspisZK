from NEF_host import *
import subprocess,hashlib
admit('NEF_FIXTURES001')
files={n:subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+n],text=True) for n in ['results/r0-opening-20261009/kats.json','results/r0-opening-20261009/transport-kat.json','results/r0-codes-20261009/kats.txt','results/r0-samplers-20261009/kats.json']}
r=py(f'''from pathlib import Path
import json,hashlib
b=Path({B!r})/'NEF_src';files=json.loads({json.dumps(files)!r})
for n,t in files.items():p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
print(json.dumps({{n:dict(sha256=hashlib.sha256((b/n).read_bytes()).hexdigest(),bytes=(b/n).stat().st_size) for n in files}}))
''');assert r.returncode==0,r.stderr;(E/'NEF_FIXTURE_PINS.json').write_text(r.stdout)
