from pathlib import Path
import subprocess,os,json,sys
E=Path(__file__).resolve().parent
jobs=[(18,'owner_success_contract','owner'),(19,'key_success_contract',None),(20,'key_success_contract','key'),(21,'length_contract',None),(22,'length_contract','data_len'),(23,'data_success_contract',None),(24,'data_success_contract','data'),(25,'data_error_contract',None),(26,'data_error_contract','data')]
for n,h,invert in jobs:
 a=f'NDG_K{n:03}';env=dict(os.environ)
 if invert:env['NDG_INVERT']=invert
 r=subprocess.run([sys.executable,str(E/'NDG_run.py'),a,'kani','r1_pool_adapter::owned::NDG_owned::'+h],env=env,capture_output=True,text=True)
 (E/(a+'-queue.log')).write_text(r.stdout+r.stderr)
 assert r.returncode==0,(a,r.stdout+r.stderr)
 rc=json.loads((E/a/'receipt.json').read_text());print(a,rc['exit_status'],flush=True)
 if rc['exit_status'] in [124,137] or 'timed out' in (E/a/'stdout.log').read_text():raise SystemExit('STOP timeout: isolate shape')
