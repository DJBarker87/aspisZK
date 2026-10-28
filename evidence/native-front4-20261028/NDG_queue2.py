from pathlib import Path
import subprocess,os,json,sys
E=Path(__file__).resolve().parent
jobs=[('NDG_K009','r1_pool_adapter::NDG_native::pool_contract',None),('NDG_K010','r1_pool_adapter::NDG_native::pool_contract','pool_program_id'),('NDG_K011','r1_pool_adapter::NDG_native::registry_contract',None),('NDG_K012','r1_pool_adapter::NDG_native::registry_contract','registry_program_id'),('NDG_K013','r1_pool_adapter::NDG_native::buffer_contract',None),('NDG_K014','r1_pool_adapter::NDG_native::buffer_contract','readonly_buffer_meta_ok'),('NDG_K015','r1_pool_adapter::NDG_native::meta_contract',None),('NDG_K016','r1_pool_adapter::NDG_native::meta_contract','readonly_meta_ok')]
for a,target,invert in jobs:
 env=dict(os.environ)
 if invert:env['NDG_INVERT']=invert
 r=subprocess.run([sys.executable,str(E/'NDG_run.py'),a,'kani',target],env=env,capture_output=True,text=True)
 (E/(a+'-queue.log')).write_text(r.stdout+r.stderr)
 assert r.returncode==0,(a,r.stdout+r.stderr)
 rc=json.loads((E/a/'receipt.json').read_text());print(json.dumps(dict(attempt=a,exit=rc['exit_status'],wall=rc['wall_seconds'],control=invert)),flush=True)
 if rc['exit_status'] in [124,137] or 'timed out' in (E/a/'stdout.log').read_text():raise SystemExit('STOP own queue on timeout; split before next related check')
