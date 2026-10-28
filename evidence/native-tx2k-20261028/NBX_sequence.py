from pathlib import Path
import json,subprocess
E=Path(__file__).resolve().parent
for i,(h,negative) in enumerate(json.loads((E/'NBX_SEQUENCE.json').read_text()),3):
 a=f'NBX_K{i:03}'
 assert not (E/a/'receipt.json').exists()
 r=subprocess.run(['python3',str(E/'NBX_native.py'),'run',a,h])
 if not (E/a/'receipt.json').exists():raise SystemExit('STOP missing receipt '+a)
 rc=json.loads((E/a/'receipt.json').read_text())
 if negative and rc['exit_status']==0:raise SystemExit('STOP negative passed '+a)
 if not negative and rc['exit_status']!=0:raise SystemExit('STOP isolate failed positive '+a)
 print('SEQUENCE',a,negative,rc['exit_status'],flush=True)
