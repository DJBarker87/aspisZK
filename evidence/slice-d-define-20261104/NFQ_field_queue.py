from pathlib import Path
import subprocess,os,sys,json
E=Path(__file__).resolve().parent
for start,target in [(23,'cm_contract'),(25,'qm_contract')]:
 for delta in [0,1]:
  a=f'NFQ_K{start+delta:03}';env=dict(os.environ,NFQ_CORE='1')
  if delta:env['NFQ_INVERT']='1'
  r=subprocess.run([sys.executable,str(E/'NFQ_run.py'),a,'kani','field::NFQ_field::'+target],env=env,capture_output=True,text=True)
  (E/(a+'-queue.log')).write_text(r.stdout+r.stderr)
  rc=json.loads((E/a/'receipt.json').read_text());out=(E/a/'stdout.log').read_text()
  assert rc['exit_status']==delta,(a,rc['exit_status'])
  assert 'VERIFICATION:- '+('FAILED' if delta else 'SUCCESSFUL') in out
  print(json.dumps(dict(attempt=a,exit=rc['exit_status'],wall=rc['wall_seconds'])),flush=True)
