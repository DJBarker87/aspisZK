from pathlib import Path
import subprocess,sys,os,json
E=Path(__file__).resolve().parent

def run(i,h,inv=False,call=None,empty=False,expected=None):
 env=dict(os.environ)
 if inv:env['NFW_INVERT']='1'
 if empty:env['NFW_EMPTY_RHO']='1'
 if call is not None:env['NFW_CALL']=str(call)
 a=f'NFW_K{i:03}';r=subprocess.run([sys.executable,str(E/'NFW_run.py'),a,'kani',h],env=env,capture_output=True,text=True)
 (E/(a+'-queue.log')).write_text(r.stdout+r.stderr);p=E/a/'stdout.log';out=p.read_text() if p.exists() else ''
 want=int(inv) if expected is None else expected
 good=r.returncode==want and 'timed out' not in out.lower() and (want==0 or 'Failed Checks:' in out)
 print(a,h,r.returncode,'matched' if good else 'OPEN',r.stdout[:170],flush=True)
 with (E/'NFW_NATIVE_QUEUE_RESULTS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,harness=h,call=call,empty_rho=empty,invert=inv,expected=want,matched=good,timeout='timed out' in out.lower()))+'\n')
 return good

if not run(61,'verifier::NFW_prepared::prepared_facet17',call=5,empty=True):raise SystemExit('new empty-rho cut needs review')
run(62,'verifier::NFW_prepared::prepared_facet17',True,5,True)
for facet in range(5,16):
 i=63+(facet-5)*2
 if run(i,f'verifier::NFW_prepared::prepared_facet{facet}'):run(i+1,f'verifier::NFW_prepared::prepared_facet{facet}',True)
 else:raise SystemExit('field cut needs review, next field is independent')
subprocess.run([sys.executable,str(E/'NFW_prefix_prepare.py')],check=True)
for j,h in enumerate(['verifier::candidate::NFW_prefix::prepare_error_root','r1_semantic::NFW_semantic_prefix::verify_error_root','verifier::candidate::NFW_prefix::tx1_error_root','verifier::candidate::NFW_prefix::tx2_error_root']):
 i=85+j*3
 if not run(i,h):raise SystemExit('prefix failure needs review before next family')
 run(i+1,h,True);run(i+2,h+'_renamed')
if run(97,'verifier::NFW_prepared::copy_q'):run(98,'verifier::NFW_prepared::copy_q',True)
# The final two slots are reserved for the exact two-extend folded payload copy.
if run(99,'verifier::NFW_prepared::copy_folded'):run(100,'verifier::NFW_prepared::copy_folded_wrong',expected=1)
