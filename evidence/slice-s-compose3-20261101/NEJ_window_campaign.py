"""Serial, control-paired per-field checks; timeouts are recorded, never retried."""
from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
plan=[(1,'negative')]+[(s,m) for s in [2,3,0,4,5,6,7,8,9] for m in ['positive','negative']]
for number,(slot,mode) in enumerate(plan,6):
 a=f'NEJ_K{number:03}'
 subprocess.run([sys.executable,str(E/'NEJ_prepare_window.py'),str(slot),mode],check=True)
 (E/(a+'-window.json')).write_bytes((E/'NEJ_WINDOW_CURRENT.json').read_bytes())
 r=subprocess.run([sys.executable,str(E/'NEJ_kani_run.py'),a,'kani','pool_v1::payment_relation::NEJ_common_window::common_window'],capture_output=True,text=True)
 print(r.stdout[-1300:],r.stderr,flush=True)
 if not (E/a/'receipt.json').exists():raise SystemExit('STOP unresolved launch or infrastructure; no later submission')
 rc=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text()
 result=dict(attempt=a,slot=slot,mode=mode,exit=rc['exit_status'],pass_verdict='VERIFICATION:- SUCCESSFUL' in log,failed_verdict='VERIFICATION:- FAILED' in log,timeout='timed out' in log.lower() or rc['exit_status']==124)
 with (E/'NEJ_WINDOW_SEQUENCE.jsonl').open('a') as f:f.write(json.dumps(result)+'\n')
 if result['timeout']:
  print('Window timed out: leave paired shape open and continue independent statement; never resubmit.',flush=True)
 if rc['exit_status'] and not result['failed_verdict'] and not result['timeout']:raise SystemExit('STOP own compiler/gate error for repair')
