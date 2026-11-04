"""Sequential per-field checks. Any timeout stops the family before controls."""
from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
for slot in range(14):
 for control,mode in enumerate(['positive','value']):
  n=3+2*slot+control;a=f'NFD_K{n:03}'
  if (E/a/'receipt.json').exists():continue
  subprocess.run([sys.executable,str(E/'NFD_prepare_request.py'),str(slot),mode],check=True)
  (E/(a+'-shape.json')).write_bytes((E/'NFD_REQUEST_CURRENT.json').read_bytes())
  r=subprocess.run([sys.executable,str(E/'NFD_kani_run.py'),a,'kani','pool_v1::pair_forest_terminal::NFD_request::request'])
  assert (E/a/'receipt.json').exists(),'recover submitted receipt read-only'
  rc=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text()
  print(json.dumps(dict(attempt=a,slot=slot,mode=mode,exit=rc['exit_status'])),flush=True)
  if 'timed out' in log.lower() or rc['exit_status'] in [124,137]:raise SystemExit('TIMEOUT family stopped: review/redesign before any further check')
  if mode=='positive':assert rc['exit_status']==0,'positive failure: inspect'
  else:assert rc['exit_status']==1 and 'Failed Checks:' in log,'control did not fail assertion'
