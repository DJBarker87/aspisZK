"""Serial own-input queue. Stop on any unexpected result; no timeout replay."""
from pathlib import Path
import sys,subprocess,json
E=Path(__file__).resolve().parent
for spec in sys.argv[1:]:
 a,kind=spec.split(':');r=subprocess.run(['python3',str(E/'PCG_run.py'),a]);assert r.returncode==0,('client refused or failed',a,r.returncode)
 x=json.loads((E/a/'receipt.json').read_text());s=(E/a/'stdout.log').read_text();rc=x['exit_status']
 if kind=='pass':assert rc==0 and 'VERIFICATION:- SUCCESSFUL' in s,(a,rc)
 elif kind=='fail':
  assertion=('Failed Checks: assertion failed' in s) or ('Failed Checks: This is a placeholder message' in s and 'core::panicking::assert_failed_inner' in s)
  assert rc==1 and assertion and 'VERIFICATION:- FAILED' in s and 'unwinding assertion' not in s,(a,rc)
 elif kind=='no_panic':assert rc==1 and 'VERIFICATION:- FAILED' in s and 'panic' in s,(a,rc)
 elif kind=='zero':assert rc==0,(a,rc)
 else:raise RuntimeError('unrecognized expected result')
