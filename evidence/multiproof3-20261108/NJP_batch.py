"""Owned serial queue: every unexpected status stops; never resubmit a scope."""
from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
for a in sys.argv[1:]:
 x=json.loads((E/(a+'.json')).read_text());expected=1 if x.get('expected_failure') else 0
 rc=subprocess.call([sys.executable,str(E/'NJP_run.py'),a])
 if rc!=expected:print('STOP '+a+' unexpected '+str(rc),flush=True);sys.exit(2)
