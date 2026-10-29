from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
a=50
for shape in ['box','stmt']:
 for stage in ['contract','inverted','real','unimplied','modifies']:
  env=dict(os.environ,NDM_FIDELITY='1')
  if stage=='inverted':env['NDM_FIDELITY_INVERT']='1'
  if stage=='modifies':env['NDM_BAD_MODIFIES']='1'
  name=f'NDM_K{a:03d}';suffix='contract' if stage in ['contract','inverted','modifies'] else stage
  target='r1_pool_adapter::NDM_fidelity::shape_'+shape+'_'+suffix
  r=subprocess.run(['python3',str(E/'NDM_run.py'),name,'kani',target],env=env,capture_output=True,text=True)
  print(json.dumps(dict(attempt=name,shape=shape,stage=stage,runner_exit=r.returncode,output=r.stdout[-2800:],stderr=r.stderr[-1600:])),flush=True)
  if r.returncode:raise SystemExit(r.returncode)
  a+=1
