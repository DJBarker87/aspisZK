from PCD_formal import *
import lzma
files={n:(E/n).read_text() for n in ['PCD_aeneas_request.py','PCD_REQUEST_LLBC_INPUT.json']}
files['PCD_frozen_request.llbc']=lzma.decompress((E/'PCD_frozen_request.llbc.xz').read_bytes()).decode()
r=run('PCD_E009','extraction','Aeneas-only actual structured frozen POOL:314 body at pinned LLBC hash',['python3','PCD_aeneas_request.py'],files)
rr=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});names=[b/'PCD_REQUEST_AENEAS_PINS.json']+list((b/'PCD_request_extracted').rglob('*.lean'))
print(json.dumps({{str(p.relative_to(b)):p.read_text() for p in names if p.is_file()}}))
''');assert rr.returncode==0,rr.stderr
for n,t in json.loads(rr.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
print('PCD actual-body Aeneas diagnostics and any partial emission recovered; no row promotion inferred.')
sys.exit(r['exit_status'])
