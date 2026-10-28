from pathlib import Path
import json,subprocess
E=Path(__file__).resolve().parent
skip_control=False
for i,(h,negative) in enumerate(json.loads((E/'NBX_MORE_SEQUENCE.json').read_text()),23):
 a=f'NBX_K{i:03}'
 if negative and skip_control:
  print('SKIP timed-out/memory-killed shape control',a,flush=True);skip_control=False;continue
 assert not (E/a/'receipt.json').exists()
 r=subprocess.run(['python3',str(E/'NBX_native.py'),'run',a,h])
 if not (E/a/'receipt.json').exists():raise SystemExit('STOP missing receipt '+a)
 rc=json.loads((E/a/'receipt.json').read_text())
 if negative and rc['exit_status']==0:raise SystemExit('STOP negative passed '+a)
 out=(E/a/'stdout.log').read_text()
 if 'error[E' in out or 'could not compile' in out:raise SystemExit('STOP repair own compile inputs '+a)
 if not negative and rc['exit_status']!=0:
  skip_control=True
 # Timeouts/failures are excluded, never rerun; continue independent members.
 print('SEQUENCE',a,negative,rc['exit_status'],flush=True)
