from NMW_formal import *
import base64
modules=['NMW_Outcome','NMW_Emitted','NMW_Symbolic','NMW_Branches','NMW_FullDispatch','NMW_RowSpecs','NMW_Fold','NMW_Commands','NMW_Projection','NMW_Footprint','NMW_Carrier','NMW_EntryFold','NMW_Transport','NMW_RouteFolds','NMW_COMBINED_IMPORT']
(E/'NMW_EXPORT_MODULES.json').write_text(json.dumps(modules))
admission('NMW_final_transport')
p=E.parent/'ledger24-20261110/NLX_CLOSURE_PINS.json.xz'
r=ssh('python3',f'''from pathlib import Path
import base64
Path({(B+'/NMW_PREDECESSOR_PINS.json.xz')!r}).write_bytes(base64.b64decode({base64.b64encode(p.read_bytes()).decode()!r}))''');assert r.returncode==0,r.stderr
r=run('NMW_L028','inspect','retention',['python3','NMW_finalize_host.py'],{n:(E/n).read_text() for n in ['NMW_finalize_host.py','NMW_EXPORT_MODULES.json']});assert r['exit_status']==0
r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});print(json.dumps({{str(p.relative_to(b)):p.read_text() for p in [b/'NMW_native/NMW_ProofDriver.c']}}))''');assert r.returncode==0,r.stderr
for n,s in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(exist_ok=True);p.write_text(s)
