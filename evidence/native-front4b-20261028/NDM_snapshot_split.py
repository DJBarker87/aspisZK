from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
a=65
for part in ['descriptor','byte']:
 for inverted in [False,True]:
  env=dict(os.environ,NDM_SNAPSHOT_PART=part)
  if inverted:env['NDM_INVERT']='1'
  else:env.pop('NDM_INVERT',None)
  name=f'NDM_K{a:03d}';target='r1_pool_adapter::owned::NDM_snapshot::snapshot_copy_input'
  r=subprocess.run(['python3',str(E/'NDM_run.py'),name,'kani',target],env=env,capture_output=True,text=True)
  print(json.dumps(dict(attempt=name,part=part,inverted=inverted,runner_exit=r.returncode,output=r.stdout[-2300:],stderr=r.stderr[-1300:])),flush=True)
  if r.returncode:raise SystemExit(r.returncode)
  a+=1
  receipt=json.loads((E/name/'receipt.json').read_text())
  if not inverted and receipt['exit_status']!=0:
   print(json.dumps(dict(skip_control=part,reason='split positive failed')),flush=True);break
