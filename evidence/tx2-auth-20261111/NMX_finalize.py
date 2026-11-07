from NMX_formal import *
import base64
admission('NMX_final_transport')
p=E.parent/'ledger24-20261110/NLX_CLOSURE_PINS.json.xz'
r=ssh('python3',f'''from pathlib import Path
import base64
Path({(B+'/NMX_PREDECESSOR_PINS.json.xz')!r}).write_bytes(base64.b64decode({base64.b64encode(p.read_bytes()).decode()!r}))''');assert r.returncode==0,r.stderr
r=run('NMX_L481','inspect','retention',['python3','NMX_finalize_host.py'],{n:(E/n).read_text() for n in ['NMX_finalize_host.py','NMX_EXPORT_MODULES.json','NMX_NMS_CANONICAL_SEED.json']});assert r['exit_status']==0
r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});print(json.dumps({{str(p.relative_to(b)):p.read_text() for p in [b/'NMX_native/NMX_ProofDriver.c']}}))''');assert r.returncode==0,r.stderr
for n,s in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(exist_ok=True);p.write_text(s)
