"""Per-copy one-iteration checks after K011/K013 full-window timeouts."""
from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
for number,(slot,mode) in enumerate([(s,m) for s in [0,4,5,6,7,8,9] for m in ['positive','negative']],14):
 a=f'NEJ_K{number:03}'
 subprocess.run([sys.executable,str(E/'NEJ_prepare_step.py'),str(slot),mode],check=True)
 (E/(a+'-window.json')).write_bytes((E/'NEJ_WINDOW_CURRENT.json').read_bytes())
 r=subprocess.run([sys.executable,str(E/'NEJ_kani_run.py'),a,'kani','pool_v1::payment_relation::NEJ_common_window::common_window'],capture_output=True,text=True)
 print(r.stdout[-1300:],r.stderr,flush=True)
 if not (E/a/'receipt.json').exists():raise SystemExit('STOP unresolved launch/infrastructure; no later submission')
 rc=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text()
 result=dict(attempt=a,slot=slot,mode=mode,exit=rc['exit_status'],one_iteration=True,pass_verdict='VERIFICATION:- SUCCESSFUL' in log,failed_verdict='VERIFICATION:- FAILED' in log,timeout='timed out' in log.lower() or rc['exit_status']==124)
 with (E/'NEJ_WINDOW_SEQUENCE.jsonl').open('a') as f:f.write(json.dumps(result)+'\n')
 if mode=='positive' and not result['pass_verdict']:raise SystemExit('OPEN step: inspect and split before any dependent window')
 if mode=='negative' and (not result['failed_verdict'] or result['timeout']):raise SystemExit('OPEN control: no paired credit')
