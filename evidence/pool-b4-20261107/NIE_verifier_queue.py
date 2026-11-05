from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent;sys.dont_write_bytecode=True;sys.path.insert(0,str(E))
from NIE_verifier_prepare import prepare
for n,control in enumerate(['none','reply','flag','borrow','identity'],107):
 a=f'NIE_K{n:03}';prepare(control)
 with (E/(a+'-client.log')).open('w') as f:r=subprocess.run([sys.executable,str(E/'NIE_kani_run.py'),a,'pair_forest_dispatch::NIE_native::association'],stdout=f,stderr=subprocess.STDOUT)
 p=E/a/'receipt.json'
 if not p.exists():raise SystemExit('Client failure; details retained: '+a)
 x=json.loads(p.read_text());s=(p.parent/'stdout.log').read_text();negative=control!='none'
 row=dict(attempt=a,family='verifier-alias',expected='FAIL' if negative else 'PASS',exit=x['exit_status'],success='SUCCESSFUL' in s,semantic_failure='VERIFICATION' in s and 'FAILED' in s,timeout='timed out' in s or x['exit_status']==124,compiler='could not compile' in s,wall=x['wall_seconds'])
 with (E/'NIE_CAMPAIGN.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
 print(json.dumps(row),flush=True)
 if row['timeout'] or row['compiler'] or row['success']==negative:raise SystemExit('Review required; no unchanged rerun')
