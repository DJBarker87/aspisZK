from PCD_formal import *
a=sys.argv[1]
r=run(a,'extraction','POOL:320 borrow-minimal checked increment, frontier step and record construction', ['python3','PCD_extract.py'], {n:(E/n).read_text() for n in ['PCD_extract.py','PCD_lane_reference.rs']})
rr=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});names=[b/'PCD_EXTRACTION_PINS.json']+list((b/'PCD_extracted').rglob('*.lean'))
print(json.dumps({{str(p.relative_to(b)):p.read_text() for p in names if p.is_file()}}))
''');assert rr.returncode==0,rr.stderr
for n,t in json.loads(rr.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
print('PCD extraction receipt and generated sources recovered; no native credit claimed.')
