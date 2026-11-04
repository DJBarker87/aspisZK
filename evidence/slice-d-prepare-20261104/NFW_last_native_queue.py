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

subprocess.run([sys.executable,str(E/'NFW_wire_errors_prepare.py')],check=True)
h='verifier::candidate::NFW_prefix::prepare_error_root'
if run(90,h):
 run(91,h,True);run(92,h+'_renamed')
else:raise SystemExit('all-error native shape needs review; copy windows independent')
for i,h in [(93,'copy_q'),(95,'copy_point'),(97,'copy_queries')]:
 if run(i,'verifier::NFW_prepared::'+h):run(i+1,'verifier::NFW_prepared::'+h,True)
 else:raise SystemExit('copy window needs review; no unchanged repeat')
if run(99,'verifier::NFW_prepared::copy_folded'):run(100,'verifier::NFW_prepared::copy_folded_wrong',expected=1)
