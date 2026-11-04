"""Sequential, bounded independent return-field checks and matched controls."""
from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
for slot in range(26):
 for mode in ['positive','value']:
  a=f'NEY_K{slot*2+(1 if mode=="positive" else 2):03}'
  if (E/a/'receipt.json').exists():continue
  subprocess.run([sys.executable,str(E/'NEY_prepare_terminal.py'),str(slot),mode],check=True)
  (E/(a+'-shape.json')).write_bytes((E/'NEY_TERMINAL_CURRENT.json').read_bytes())
  r=subprocess.run([sys.executable,str(E/'NEY_kani_run.py'),a,'kani','pool_v1::pair_forest_terminal::NEY_terminal::terminal'])
  assert (E/a/'receipt.json').exists(),'No receipt: stop, recover read-only'
  rc=json.loads((E/a/'receipt.json').read_text())
  print(json.dumps(dict(attempt=a,slot=slot,mode=mode,exit=rc['exit_status'])),flush=True)
  if rc['exit_status'] not in [0,1,124]:raise SystemExit('Non-verdict: inspect before another launch')
