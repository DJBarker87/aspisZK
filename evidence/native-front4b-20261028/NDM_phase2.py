from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
a=31
jobs=[('candidate_frontier_value','r1_pool_adapter::NDM_native::common_contract'),('candidate_frontier_frame','r1_pool_adapter::NDM_native::common_contract'),('scalar','r1_pool_adapter::NDM_native::common_contract'),('master','r1_pool_adapter::NDM_native::common_contract'),('scalar','r1_pool_adapter::owned::NDM_owned::zero_advance'),('scalar','r1_pool_adapter::owned::NDM_owned::zero_reject'),('scalar','r1_pool_adapter::owned::NDM_owned::zero_terminal')]
for window,target in jobs:
 for inverted in [False,True]:
  name=f'NDM_K{a:03d}';env=dict(os.environ,NDM_WINDOW=window)
  if inverted:env['NDM_INVERT']='1'
  else:env.pop('NDM_INVERT',None)
  r=subprocess.run(['python3',str(E/'NDM_run.py'),name,'kani',target],env=env,capture_output=True,text=True)
  print(json.dumps(dict(attempt=name,window=window,target=target,inverted=inverted,runner_exit=r.returncode,output=r.stdout[-2400:],stderr=r.stderr[-1500:])),flush=True)
  if r.returncode:raise SystemExit(r.returncode)
  a+=1
  log=(E/name/'stdout.log').read_text().lower()
  receipt=json.loads((E/name/'receipt.json').read_text())
  if not inverted and (receipt['exit_status']!=0):
   print(json.dumps(dict(skip_control=target,positive=name,reason='positive not established; no same-shape control launch')),flush=True)
   break
