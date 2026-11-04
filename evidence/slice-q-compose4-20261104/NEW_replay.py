"""Sequential own re-establishment, stop at any unexpected result; never retries a scope."""
from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
selected=set(sys.argv[1:])
for row in json.loads((E/'NEW_OFFLINE_REPLAY_PLAN.json').read_text()):
 a=row['attempt']
 if selected and a not in selected:continue
 assert not (E/a).exists(),('Never rerun an existing scope',a)
 r=subprocess.run([sys.executable,str(E/'NEW_kani.py'),a,row['harness'],*row['flags']],capture_output=True,text=True)
 (E/(a+'.driver.log')).write_text(r.stdout+r.stderr)
 print(r.stdout[-1500:],flush=True)
 assert r.returncode==row['want'],(a,r.returncode,row['want'])
 log=(E/a/'stdout.log').read_text()
 assert ('VERIFICATION:- SUCCESSFUL' if not row['want'] else 'VERIFICATION:- FAILED')in log,(a,'not a verification verdict')
 assert 'TIMEOUT' not in log and 'timed out' not in log.lower() and 'internal compiler error' not in log,(a,'OPEN')
 receipt=json.loads((E/a/'receipt.json').read_text())
 assert receipt['env']['CARGO_NET_OFFLINE']=='true'
