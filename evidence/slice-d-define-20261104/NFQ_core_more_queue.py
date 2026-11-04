from pathlib import Path
import subprocess,os,sys,json
E=Path(__file__).resolve().parent
for i,target,expected,invert in [(28,'prep_copy_negative',1,False),(29,'reduce_contract',0,False),(30,'reduce_contract',1,True),(31,'prep_contract',0,False),(32,'prep_contract',1,True)]:
 a=f'NFQ_K{i:03}';env=dict(os.environ,NFQ_CORE='1')
 if invert:env['NFQ_INVERT']='1'
 r=subprocess.run([sys.executable,str(E/'NFQ_run.py'),a,'kani','field::NFQ_field::'+target],env=env,capture_output=True,text=True)
 (E/(a+'-queue.log')).write_text(r.stdout+r.stderr)
 rc=json.loads((E/a/'receipt.json').read_text());out=(E/a/'stdout.log').read_text()
 assert rc['exit_status']==expected and 'VERIFICATION:- '+('FAILED' if expected else 'SUCCESSFUL') in out,(a,'Unexpected verdict',rc['exit_status'])
 print(json.dumps(dict(attempt=a,exit=rc['exit_status'],wall=rc['wall_seconds'])),flush=True)
