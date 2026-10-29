from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
a=45
for name in ['snapshot_copy_input','snapshot_deferred_error','snapshot_failed_borrow']:
 target='r1_pool_adapter::owned::NDM_snapshot::'+name
 for inverted in [False,True]:
  attempt=f'NDM_K{a:03d}';env=dict(os.environ)
  if inverted:env['NDM_INVERT']='1'
  else:env.pop('NDM_INVERT',None)
  r=subprocess.run(['python3',str(E/'NDM_run.py'),attempt,'kani',target],env=env,capture_output=True,text=True)
  print(json.dumps(dict(attempt=attempt,target=target,inverted=inverted,runner_exit=r.returncode,output=r.stdout[-2400:],stderr=r.stderr[-1600:])),flush=True)
  if r.returncode:raise SystemExit(r.returncode)
  a+=1
  receipt=json.loads((E/attempt/'receipt.json').read_text())
  if not inverted and receipt['exit_status']!=0:
   print(json.dumps(dict(skip_control=target,reason='positive failed; new split needed')),flush=True);break
