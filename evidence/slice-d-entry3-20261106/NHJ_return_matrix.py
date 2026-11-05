"""Sequential new after-copy domains; never resubmit a passing or failed attempt."""
from pathlib import Path
import subprocess,sys,json,lzma
E=Path(__file__).resolve().parent
for i,n in enumerate([1768,1880,384,192,768,128,256,320]):
 pos=f'NHJ_K{17+2*i:03}';neg=f'NHJ_K{18+2*i:03}'
 for a,suffix,exit in [(pos,'',0),(neg,'_corrupt',1)]:
  if (E/a/'receipt.json').exists():raise RuntimeError('Existing attempt; matrix never resubmits')
  r=subprocess.run([sys.executable,str(E/'NHJ_run.py'),a,'kani',f'r1_pool_adapter::owned::NHJ_owned::returned_header_{n}{suffix}'],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
  (E/(a+'-controller.log')).write_text(r.stdout)
  p=E/a/'receipt.json'
  if not p.exists():raise RuntimeError('No terminal receipt; infrastructure or transport must be reviewed, never resubmit')
  receipt=json.loads(p.read_text());s=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
  semantic=('VERIFICATION:- SUCCESSFUL' in s) if exit==0 else ('VERIFICATION:- FAILED' in s and 'assignable' in s and 'Failed Checks:' in s and 'timed out' not in s)
  row=dict(attempt=a,length=n,expected_exit=exit,actual_exit=receipt['exit_status'],semantic=semantic)
  with (E/'NHJ_RETURN_MATRIX.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
  print(json.dumps(row),flush=True)
  if receipt['exit_status']!=exit or not semantic:
   print('Uncredited member; next independent size only',flush=True)
   if exit==0:break
