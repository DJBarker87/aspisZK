from pathlib import Path
import subprocess,os,json,sys
E=Path(__file__).resolve().parent
jobs=[(22,'length_ok_contract',None),(23,'length_ok_contract','data_len'),(24,'length_error_contract',None),(25,'length_error_contract','data_len'),(26,'data_success_contract',None),(27,'data_success_contract','data'),(28,'data_error_contract',None),(29,'data_error_contract','data')]
for n,h,invert in jobs:
 a=f'NDG_K{n:03}';env=dict(os.environ)
 if invert:env['NDG_INVERT']=invert
 r=subprocess.run([sys.executable,str(E/'NDG_run.py'),a,'kani','r1_pool_adapter::owned::NDG_owned::'+h],env=env,capture_output=True,text=True)
 (E/(a+'-queue.log')).write_text(r.stdout+r.stderr)
 assert r.returncode==0,(a,r.stdout+r.stderr)
 rc=json.loads((E/a/'receipt.json').read_text());print(a,rc['exit_status'],flush=True)
 if rc['exit_status'] in [124,137] or 'timed out' in (E/a/'stdout.log').read_text():raise SystemExit('STOP timeout: isolate shape')
