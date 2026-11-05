"""Sequential per-label (al) controls/stability; never retry a completed shape."""
from pathlib import Path
import subprocess,json,lzma,sys,re
E=Path(__file__).resolve().parent
jobs=[(12,'callback_parse_wrong',False),(13,'callback_parse_stability',True)]
for i,label in enumerate(['semantic','transcript','relation','merkle','query','checkpoint','allocation']):
 jobs.extend([(14+2*i,'callback_'+label,True),(15+2*i,'callback_'+label+'_wrong',False)])
rows=[]
for k,name,positive in jobs:
 a=f'NHY_K{k:03}';p=E/a/'receipt.json'
 if p.exists():
  r=json.loads(p.read_text());print('reuse terminal '+a,flush=True)
 else:
  subprocess.run([sys.executable,str(E/'NHY_run.py'),a,'kani','NHY_error::'+name],stdout=sys.stdout,stderr=sys.stderr)
  assert p.exists(),'missing terminal receipt: recover read-only, do not resubmit'
  r=json.loads(p.read_text())
 s=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 valid=r['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in s if positive else r['exit_status']==1 and 'VERIFICATION:- FAILED' in s and 'timed out' not in s and re.search(r'\*\* 1 of \d+ failed',s) and re.search(r'Failed Checks: \|r\|\s*\*r',s)
 rows.append(dict(attempt=a,harness=name,expected='PASS' if positive else 'semantic FAIL',valid=bool(valid)))
 (E/'NHY_CALLBACK_MATRIX.json').write_text(json.dumps(dict(status='RUNNING' if valid else 'STOP',rows=rows),indent=1)+'\n')
 if not valid:sys.exit(1)
(E/'NHY_CALLBACK_MATRIX.json').write_text(json.dumps(dict(status='PASS_CALLBACKS_ONLY',rows=rows,baseline='NHY_K011',no_String_or_syscall_credit=True),indent=1)+'\n')
