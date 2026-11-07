"""Own fail-closed sequencing: inspect each semantic verdict before the next admission."""
from pathlib import Path
import json,sys,subprocess
E=Path(__file__).resolve().parent
for item in sys.argv[1:]:
 a,expected=item.split(':',1)
 r=subprocess.run([sys.executable,str(E/'PCF_run.py'),a])
 if r.returncode:raise SystemExit(r.returncode)
 x=json.loads((E/a/'receipt.json').read_text());s=(E/a/'stdout.log').read_text()
 assert 'timed out' not in s.lower() and x['exit_status'] not in [124,137],a+': stop after timeout/memory pressure'
 assert 'internal compiler error' not in s and not any(l.startswith('error:') for l in s.splitlines()),a+': compiler failure, no continuation'
 assert ('VERIFICATION:- SUCCESSFUL' if expected=='PASS' else 'VERIFICATION:- FAILED') in s,a+': unexpected semantic verdict'
 assert x['exit_status']==(0 if expected=='PASS' else 1),a
 if expected!='PASS':assert 'Failed Checks:' in s,a+': negative has no semantic failed check'
 if expected=='FRAME':assert 'assignable' in s,a+': frame control did not detect assignability violation'
 print(a+' semantic '+expected+' confirmed',flush=True)
