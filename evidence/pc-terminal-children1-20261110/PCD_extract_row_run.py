from PCD_formal import *
a=sys.argv[1]
r=run(a,'extraction','POOL:320 full borrow-minimal reference with complete Result and fixed loop', ['python3','PCD_extract_row.py'], {n:(E/n).read_text() for n in ['PCD_extract_row.py','PCD_full_lane_reference.rs']})
rr=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});names=[b/'PCD_ROW_EXTRACTION_PINS.json']+list((b/'PCD_row_extracted').rglob('*.lean'))
print(json.dumps({{str(p.relative_to(b)):p.read_text() for p in names if p.is_file()}}))
''');assert rr.returncode==0,rr.stderr
for n,t in json.loads(rr.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
print('PCD extraction receipt and generated sources recovered; no native credit claimed.')
