from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
for n,mode in enumerate(['unimplied','contract','inverted','frame'],30):
 a=f'NEJ_K{n:03}'
 subprocess.run([sys.executable,str(E/'NEJ_prepare_step_shape.py'),mode],check=True)
 (E/(a+'-shape.json')).write_bytes((E/'NEJ_SHAPE_CURRENT.json').read_bytes())
 r=subprocess.run([sys.executable,str(E/'NEJ_kani_run.py'),a,'kani','pool_v1::payment_relation::NEJ_common_window::common_window'],capture_output=True,text=True);print(r.stdout[-1300:],r.stderr,flush=True)
 if not (E/a/'receipt.json').exists():raise SystemExit('STOP unresolved attempt')
 rc=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text()
 success=mode in ['native','contract']
 if ('VERIFICATION:- SUCCESSFUL' in log)!=success or 'timed out' in log.lower() or (not success and 'Failed Checks:' not in log):raise SystemExit('OPEN shape control; inspect, do not credit')
