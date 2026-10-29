from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
a=78
for target in ['r1_pool_adapter::owned::NDM_calls::lane_input','r1_pool_adapter::NDM_native::scan_input']:
 for negative in [False,True]:
  env=dict(os.environ,NDM_CALL_PROBE='1')
  if negative:env['NDM_PROBE_INVERT']='1'
  name=f'NDM_K{a:03d}'
  r=subprocess.run(['python3',str(E/'NDM_run.py'),name,'kani',target],env=env,capture_output=True,text=True)
  print(json.dumps(dict(attempt=name,target=target,negative=negative,runner_exit=r.returncode,output=r.stdout[-2300:],stderr=r.stderr[-1500:])),flush=True)
  if r.returncode:raise SystemExit(r.returncode)
  a+=1
  receipt=json.loads((E/name/'receipt.json').read_text())
  if not negative and receipt['exit_status']!=0:
   print(json.dumps(dict(skip_control=target,reason='positive failed')),flush=True);break
