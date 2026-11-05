"""One scope at a time; preserve every failure, never repeat an allocated ID."""
from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
start=int(sys.argv[1]);cases=sys.argv[2:]
for i,(kind,mode) in enumerate((k,m) for k in cases for m in ['positive','negative']):
 a='NHP_K'+str(start+i).zfill(3)
 assert not (E/a).exists(),a
 gen=subprocess.run([sys.executable,str(E/'NHP_metadata.py'),mode,kind],capture_output=True,text=True)
 assert gen.returncode==0,gen.stderr
 harness=gen.stdout.strip().splitlines()[-1]
 run=subprocess.run([sys.executable,str(E/'NHP_kani_run.py'),a,harness],capture_output=True,text=True)
 (E/(a+'-client.log')).write_text(run.stdout+run.stderr)
 p=E/a/'receipt.json'
 if not p.exists():print(json.dumps(dict(attempt=a,status='UNRESOLVED CLIENT; stop campaign')),flush=True);sys.exit(1)
 out=(E/a/'stdout.log').read_text();receipt=json.loads(p.read_text())
 expected='VERIFICATION:- SUCCESSFUL' if mode=='positive' else 'VERIFICATION:- FAILED'
 admitted=receipt['exit_status']==(0 if mode=='positive' else 1) and expected in out
 result=dict(attempt=a,kind=kind,mode=mode,exit=receipt['exit_status'],expected_verdict_observed=admitted,failed_checks=[l for l in out.splitlines() if l.startswith('Failed Checks:')],compiler_errors=[l for l in out.splitlines() if l.startswith('error')],production_credit=False)
 with (E/'NHP_CAMPAIGN.jsonl').open('a') as f:f.write(json.dumps(result)+'\n')
 print(json.dumps({k:result[k] for k in ['attempt','kind','mode','exit','expected_verdict_observed']}),flush=True)
 if not admitted:
  print('Unexpected result retained; inspect and change the shape before any further attempt.',flush=True);sys.exit(2)
