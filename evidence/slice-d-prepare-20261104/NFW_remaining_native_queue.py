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

def prep(name):
 subprocess.run([sys.executable,str(E/name)],check=True)

# Fresh same-source call0 pair replaces the older source-different fragment.
a=run(48,'verifier::NFW_prepared::prepared_facet16',call=0)
if a:run(49,'verifier::NFW_prepared::prepared_facet16',True,0)
else:raise SystemExit('state0 window needs review before a control')
prep('NFW_prepared_payload_prepare.py');prep('NFW_prepared_copy_prepare.py');prep('NFW_prepared_native_prepare.py')
# Independent exact call positions. A timeout is recorded, never rerun unchanged.
for call in range(6):
 i=50+call*2
 if run(i,'verifier::NFW_prepared::prepared_facet17',call=call):
  run(i+1,'verifier::NFW_prepared::prepared_facet17',True,call)
 else:raise SystemExit('payload window needs review; next independent facet remains available')
for facet in range(5,16):
 i=62+(facet-5)*2
 if run(i,f'verifier::NFW_prepared::prepared_facet{facet}'):
  run(i+1,f'verifier::NFW_prepared::prepared_facet{facet}',True)
 else:raise SystemExit('field window needs review; do not retry unchanged')
prep('NFW_prefix_prepare.py')
for j,h in enumerate(['verifier::candidate::NFW_prefix::prepare_error_root','r1_semantic::NFW_semantic_prefix::verify_error_root','verifier::candidate::NFW_prefix::tx1_error_root','verifier::candidate::NFW_prefix::tx2_error_root']):
 i=84+j*3
 if not run(i,h):raise SystemExit('prefix input or proof failure: inspect before next family')
 run(i+1,h,True)
 run(i+2,h+'_renamed')
for i,h in [(96,'copy_q'),(98,'copy_point')]:
 if run(i,'verifier::NFW_prepared::'+h):run(i+1,'verifier::NFW_prepared::'+h,True)
 else:raise SystemExit('copy control needs review')
run(100,'verifier::NFW_prepared::copy_folded_wrong',expected=1)
