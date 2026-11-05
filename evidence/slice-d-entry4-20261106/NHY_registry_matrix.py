"""Actual independent registry callees, sequential full-body/no-heap contracts."""
from pathlib import Path
import subprocess,json,lzma,sys,re
E=Path(__file__).resolve().parent;rows=[]
for i,name in enumerate(['immutable1','paused1','immutable2','paused2','retirement1','retirement2','status']):
 for bad in [False,True]:
  a=f'NHY_K{30+2*i+int(bad):03}';target='r1_pool_adapter::owned::NHY_auth::'+name+('_wrong' if bad else '')
  assert not (E/a).exists(),'completed shape must not rerun'
  subprocess.run([sys.executable,str(E/'NHY_run.py'),a,'kani',target])
  r=json.loads((E/a/'receipt.json').read_text());s=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
  valid=r['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in s if not bad else r['exit_status']==1 and 'timed out' not in s and re.search(r'\*\* 1 of \d+ failed',s) and re.search(r'Failed Checks: \|out\|\s*\*out',s)
  rows.append(dict(attempt=a,harness=target,valid=bool(valid),expected='semantic FAIL' if bad else 'PASS'))
  (E/'NHY_REGISTRY_MATRIX.json').write_text(json.dumps(dict(status='RUNNING' if valid else 'STOP',rows=rows),indent=1)+'\n')
  if not valid:sys.exit(1)
(E/'NHY_REGISTRY_MATRIX.json').write_text(json.dumps(dict(status='PASS_LOCAL_CALLEES',rows=rows),indent=1)+'\n')
