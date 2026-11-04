"""Serial independent scalar pairs; stop immediately on any unexpected verdict."""
from pathlib import Path
import subprocess,os,json,sys
E=Path(__file__).resolve().parent
jobs=[('r1_wire::NFQ_wire::shape_contract',4),('transport::NFQ_transport::folds_contract',6),('transport::NFQ_transport::final_len_contract',8),('verifier::NFQ_verifier::size_contract',10)]
for target,start in jobs:
 for delta in [0,1]:
  a=f'NFQ_K{start+delta:03}';env=dict(os.environ)
  if delta:env['NFQ_INVERT']='1'
  r=subprocess.run([sys.executable,str(E/'NFQ_run.py'),a,'kani',target],env=env,capture_output=True,text=True)
  (E/(a+'-queue.log')).write_text(r.stdout+r.stderr)
  receipt=json.loads((E/a/'receipt.json').read_text())
  out=(E/a/'stdout.log').read_text()
  assert receipt['exit_status']==delta,(a,receipt['exit_status'])
  assert ('VERIFICATION:- FAILED' in out and '1 of ' in out and 'Failed Checks: |r|' in out) if delta else 'VERIFICATION:- SUCCESSFUL' in out
  print(json.dumps(dict(attempt=a,exit=receipt['exit_status'],wall=receipt['wall_seconds'])),flush=True)
