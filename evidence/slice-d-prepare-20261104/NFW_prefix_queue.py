from pathlib import Path
import subprocess,sys,os,json
E=Path(__file__).resolve().parent

def run(i,h,inv=False,call=None,expected=None):
 env=dict(os.environ)
 if inv:env['NFW_INVERT']='1'
 if call is not None:env['NFW_CALL']=str(call)
 a=f'NFW_K{i:03}'
 r=subprocess.run([sys.executable,str(E/'NFW_run.py'),a,'kani',h],env=env,capture_output=True,text=True)
 (E/(a+'-queue.log')).write_text(r.stdout+r.stderr)
 p=E/a/'stdout.log';out=p.read_text() if p.exists() else ''
 want=int(inv) if expected is None else expected
 good=r.returncode==want and 'timed out' not in out.lower() and (want==0 or 'Failed Checks:' in out)
 print(a,h,r.returncode,'matched' if good else 'OPEN',r.stdout[:170],flush=True)
 with (E/'NFW_NATIVE_QUEUE_RESULTS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,harness=h,call=call,invert=inv,expected=want,matched=good,timeout='timed out' in out.lower()))+'\n')
 return good

# All cases are distinct: matched control/rename, then independent caller family.
run(79,'verifier::candidate::NFW_prefix::prepare_error_root',True)
run(80,'verifier::candidate::NFW_prefix::prepare_error_root_renamed')
for i,h in [(81,'r1_semantic::NFW_semantic_prefix::verify_error_root'),(84,'verifier::candidate::NFW_prefix::tx1_error_root'),(87,'verifier::candidate::NFW_prefix::tx2_error_root')]:
 ok=run(i,h)
 if ok:
  run(i+1,h,True)
  run(i+2,h+'_renamed')
 else:
  print('Review required; unchanged shape and controls skipped. Next independent family.',flush=True)
