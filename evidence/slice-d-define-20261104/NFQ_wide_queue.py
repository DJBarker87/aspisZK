from pathlib import Path
import subprocess,os,sys,json
E=Path(__file__).resolve().parent
for i,target,expected,invert in [(52,'copy_positive',0,False),(53,'copy_negative',1,False),(54,'c0_contract',0,False),(55,'c0_contract',1,True),(56,'c1_contract',0,False),(57,'c1_contract',1,True)]:
 a=f'NFQ_K{i:03}';env=dict(os.environ,NFQ_CORE='1')
 if invert:env['NFQ_INVERT']='1'
 r=subprocess.run([sys.executable,str(E/'NFQ_run.py'),a,'kani','field::wide_exact::NFQ_wide::'+target],env=env,capture_output=True,text=True)
 (E/(a+'-queue.log')).write_text(r.stdout+r.stderr)
 rc=json.loads((E/a/'receipt.json').read_text());out=(E/a/'stdout.log').read_text()
 assert rc['exit_status']==expected and 'VERIFICATION:- '+('FAILED' if expected else 'SUCCESSFUL') in out,(a,'unexpected verdict',rc['exit_status'])
 print(json.dumps(dict(attempt=a,exit=rc['exit_status'],wall=rc['wall_seconds'])),flush=True)
