"""Serial own tests; stop on any timeout, infrastructure fault or wrong verdict."""
from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
cases=[(8,'program',False),(9,'order',False),(10,'length',False),(11,'decode-arg',False),(12,'decoded-value',False),(13,'bytes',False),(14,'missing',False),(15,'cpi-error',False),(16,'decode-error',False),(17,'bad-length',True),(18,'bad-length-negative',False),(19,'copy',True),(20,'copy-negative',False)]
for n,mode,expected in cases:
 a=f'NFO_K{n:03}'
 if (E/a/'receipt.json').exists():continue
 subprocess.run([sys.executable,str(E/'NFO_native.py'),mode],check=True)
 r=subprocess.run([sys.executable,str(E/'NFO_kani_run.py'),a],capture_output=True,text=True)
 print(a,mode,'wrapper_exit',r.returncode,flush=True)
 if not (E/a/'receipt.json').exists():print(r.stdout+r.stderr);sys.exit('STOP missing receipt')
 log=(E/a/'stdout.log').read_text();receipt=json.loads((E/a/'receipt.json').read_text())
 assert receipt['exit_status']==(0 if expected else 1),(a,'wrong exit',r.stdout+r.stderr)
 assert ('VERIFICATION:- SUCCESSFUL' if expected else 'VERIFICATION:- FAILED') in log,(a,'no solver verdict')
 assert 'Failed Checks: unwinding' not in log and 'Timed out' not in log and 'TIMEOUT' not in log,(a,'excluded shape; inspect before next run')
 with (E/'NFO_CAMPAIGN.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,mode=mode,expected_success=expected,matched=True))+'\n')
