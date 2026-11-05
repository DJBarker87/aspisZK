from pathlib import Path
import subprocess,json,os,time
E=Path(__file__).resolve().parent
assert (E/'NHI_K002/receipt.json').exists(), 'Preflight pair must have returned'
assert not (E/'NHI_K003/receipt.json').exists(),'Never resubmit an existing attempt'
rows=[]
for n in range(3,121):
 a=f'NHI_K{n:03d}';g=(n-1)//2;negative=n%2==0
 env=dict(os.environ)
 if negative:env['NHI_INVERT']='1'
 else:env.pop('NHI_INVERT',None)
 with (E/(a+'-queue.log')).open('w')as f:
  result=subprocess.run(['python3',str(E/'NHI_run.py'),a,'kani',f'weights::NHI_tensor::g{g:02d}'],stdout=f,stderr=subprocess.STDOUT,env=env)
 p=E/a/'receipt.json'
 if not p.exists():raise SystemExit('STOP missing receipt; recover read-only, no resubmit '+a)
 r=json.loads(p.read_text());out=(E/a/'stdout.log').read_text()
 if 'timed out'in out.lower()or r['exit_status']in [124,137]:
  (E/'NHI_NATIVE_FAILING_STEP.json').write_text(json.dumps(dict(attempt=a,group=g,reason='timeout or memory kill; do not rerun unchanged; isolate before continuing related shape',receipt=str(p)),indent=2));raise SystemExit(2)
 expected=r['exit_status']==(1 if negative else 0) and ('Failed Checks: assertion failed: good'in out if negative else 'VERIFICATION:- SUCCESSFUL'in out)
 rows.append(dict(attempt=a,group=g,negative=negative,exit=r['exit_status'],expected=expected))
 (E/'NHI_NATIVE_QUEUE_STATUS.json').write_text(json.dumps(dict(completed=rows,all_expected=all(x['expected']for x in rows),last=a),indent=2)+'\n')
 print(a,r['exit_status'],'expected'if expected else'FINDING',flush=True)
 if not expected:raise SystemExit('STOP own input or native mismatch; inspect, no credit '+a)
