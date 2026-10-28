from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
windows=['scalar','master','checkpoint','lane','anchor','live_pool','live_domain','live_scalar','live_root','live_frontier','candidate_scalar','candidate_root','candidate_frontier']
a=5
for w in windows:
 for inverse in [False,True]:
  name=f'NDM_K{a:03d}';env=dict(os.environ,NDM_WINDOW=w)
  if inverse:env['NDM_INVERT']='1'
  else:env.pop('NDM_INVERT',None)
  r=subprocess.run(['python3',str(E/'NDM_run.py'),name,'kani','r1_pool_adapter::NDM_native::common_contract'],env=env,capture_output=True,text=True)
  print(json.dumps(dict(attempt=name,window=w,inverted=inverse,runner_exit=r.returncode,output=r.stdout[-2300:],stderr=r.stderr[-1500:])),flush=True)
  if r.returncode:raise SystemExit(r.returncode)
  a+=1
