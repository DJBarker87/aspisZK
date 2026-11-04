from pathlib import Path
import subprocess,os,sys,json
E=Path(__file__).resolve().parent
for i,target,expected,invert in [(47,'field::NFQ_field::record_real',0,False),(48,'field::NFQ_field::record_unimplied',1,False),(49,'field::NFQ_field::record_frame',1,False),(50,'state_only_hiding::NFQ_hiding::linear_contract',0,False),(51,'state_only_hiding::NFQ_hiding::linear_contract',1,True)]:
 a=f'NFQ_K{i:03}';env=dict(os.environ,NFQ_CORE='1')
 if invert:env['NFQ_INVERT']='1'
 r=subprocess.run([sys.executable,str(E/'NFQ_run.py'),a,'kani',target],env=env,capture_output=True,text=True)
 (E/(a+'-queue.log')).write_text(r.stdout+r.stderr)
 rc=json.loads((E/a/'receipt.json').read_text());out=(E/a/'stdout.log').read_text()
 assert rc['exit_status']==expected and 'VERIFICATION:- '+('FAILED' if expected else 'SUCCESSFUL') in out,(a,'unexpected verdict',rc['exit_status'])
 print(json.dumps(dict(attempt=a,exit=rc['exit_status'],wall=rc['wall_seconds'])),flush=True)
