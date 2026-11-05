from pathlib import Path
import subprocess,json,sys,lzma
E=Path(__file__).resolve().parent
for a,h,expected,check in [('NHJ_K037','to_vec_alloc_header',0,'VERIFICATION:- SUCCESSFUL'),('NHJ_K038','to_vec_alloc_header_corrupt',1,'assignable'),('NHJ_K039','to_vec_byte_window',0,'VERIFICATION:- SUCCESSFUL'),('NHJ_K040','to_vec_byte_window_corrupt',1,'Failed Checks: |r| *r'),('NHJ_K041','to_vec_finalize',0,'VERIFICATION:- SUCCESSFUL'),('NHJ_K042','to_vec_finalize_corrupt',1,'assignable')]:
 assert not (E/a/'receipt.json').exists()
 r=subprocess.run([sys.executable,str(E/'NHJ_run.py'),a,'kani','r1_pool_adapter::owned::NHJ_owned::'+h],capture_output=True,text=True);(E/(a+'-controller.log')).write_text(r.stdout+r.stderr)
 p=E/a/'receipt.json'
 if not p.exists():raise RuntimeError('No receipt; infrastructure or submitted transport recovery required; no resubmission')
 x=json.loads(p.read_text());s=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode();ok=x['exit_status']==expected and check in s and 'timed out' not in s and ('VERIFICATION:- FAILED' in s if expected else True)
 print(json.dumps(dict(attempt=a,expected=expected,exit=x['exit_status'],admitted=ok)),flush=True)
 if not ok:
  with (E/'NHJ_STD_MATRIX_FAILURES.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,exit=x['exit_status'],credited=False))+'\n')
  if expected==0:
   # Skip its paired control; move to the next independent primitive.
   skip=a
 else:skip=None
 # All attempts are distinct; failures are retained, never retried.
