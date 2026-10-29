from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
for a,stage in [(61,'inverted'),(62,'real'),(63,'unimplied'),(64,'modifies')]:
 env=dict(os.environ,NDM_FIDELITY='1',NDM_ARBITRARY='1')
 if stage=='inverted':env['NDM_FIDELITY_INVERT']='1'
 if stage=='modifies':env['NDM_BAD_MODIFIES']='1'
 suffix='contract' if stage in ['inverted','modifies'] else stage
 attempt=f'NDM_K{a:03d}';target='r1_pool_adapter::NDM_fidelity::shape_box_'+suffix
 r=subprocess.run(['python3',str(E/'NDM_run.py'),attempt,'kani',target],env=env,capture_output=True,text=True)
 print(json.dumps(dict(attempt=attempt,stage=stage,runner_exit=r.returncode,output=r.stdout[-2300:],stderr=r.stderr[-1600:])),flush=True)
 if r.returncode:raise SystemExit(r.returncode)
