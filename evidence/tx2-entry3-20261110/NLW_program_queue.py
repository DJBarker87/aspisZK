from NLW_program import native
from NLW_formal import E,lzma,json
import sys
for a,target,expected in zip(sys.argv[1::3],sys.argv[2::3],sys.argv[3::3]):
 r=json.loads((E/a/'receipt.json').read_text()) if (E/a/'receipt.json').exists() else native(a,target)
 out=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 assert 'Checking harness '+target in out,(a,'no harness verdict')
 if expected=='pass':ok=r['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in out
 else:ok=r['exit_status']!=0 and 'VERIFICATION:- FAILED' in out and 'unwinding failures' not in out and 'undetermined' not in out
 if not ok:
  print(json.dumps(dict(attempt=a,queue_stopped=True,expected=expected,reason='unexpected or incomplete verdict; inspect before continuing')))
  sys.exit(1)
 print(json.dumps(dict(attempt=a,expected_verdict=expected,matched=True)))
