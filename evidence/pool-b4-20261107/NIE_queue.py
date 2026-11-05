"""Serial owned campaign; all raw source/diagnostics stay in evidence files."""
from pathlib import Path
import subprocess,json,sys,time,re
E=Path(__file__).resolve().parent;sys.dont_write_bytecode=True;sys.path.insert(0,str(E))
from NIE_native_prepare import recheck
jobs=[(7,0,True)]+[(8+2*(c-1)+n,c,bool(n)) for c in range(1,4) for n in range(2)]
for number,case,negative in jobs:
 a=f'NIE_K{number:03}'
 recheck(case,negative)
 with (E/(a+'-client.log')).open('w') as f:r=subprocess.run([sys.executable,str(E/'NIE_kani_run.py'),a,'nullifier::NIE_native::association'],stdout=f,stderr=subprocess.STDOUT)
 p=E/a/'receipt.json'
 if not p.exists():raise SystemExit('Client failure; details retained: '+a)
 x=json.loads(p.read_text());s=(p.parent/'stdout.log').read_text()
 summary=dict(attempt=a,expected='FAIL' if negative else 'PASS',exit=x['exit_status'],success='SUCCESSFUL' in s,timeout='timed out' in s,compiler='could not compile' in s,wall=x['wall_seconds'])
 with (E/'NIE_CAMPAIGN.jsonl').open('a') as f:f.write(json.dumps(summary)+'\n')
 print(json.dumps(summary),flush=True)
 if summary['timeout'] or summary['compiler'] or summary['success']==negative:raise SystemExit('Review required; no unchanged rerun')
