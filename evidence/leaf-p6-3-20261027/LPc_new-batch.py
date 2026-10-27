from pathlib import Path
import json,subprocess,hashlib
E=Path(__file__).resolve().parent
modules=['LPc_ChunkFrame','LPc_TailTransport','LPc_DecodeCanonical','LPc_DecodeValues','LPc_DecodeSuccess','LPc_BoundaryProducer','LPc_CallerBounds','LPc_ExpandRows','LPc_ViewFrame','LPc_Nonvacuity']
for module in modules:
 receipts=[json.loads(p.read_text()) for p in sorted(E.glob('LPc_L*/receipt.json'))]
 source_hash=hashlib.sha256((E/(module+'.lean')).read_bytes()).hexdigest()
 same=[r for r in receipts if r.get('module')==module and source_hash in r['source_hashes'].values()]
 if same:
  if same[-1]['exit_status']==0:continue
  raise SystemExit('STOP unchanged failed source '+module)
 number=max(int(r['attempt'].split('_L')[1]) for r in receipts)+1
 if number>=60:raise SystemExit('STOP reserve final audit attempt')
 a=f'LPc_L{number:03}'
 subprocess.run(['python3',str(E/'LPc_attempt.py'),a,'lean',module],check=True)
 if json.loads((E/a/'receipt.json').read_text())['exit_status']!=0:raise SystemExit('STOP proof error '+a+' '+module)
