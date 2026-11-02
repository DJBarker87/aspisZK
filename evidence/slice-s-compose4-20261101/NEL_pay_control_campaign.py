from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
for n,case,mode in [(42,'withdrawal','positive'),(43,'withdrawal','negative'),(44,'transfer','negative')]:
 a=f'NEL_K{n:03}';subprocess.run([sys.executable,str(E/'NEL_prepare_payment_validator.py'),case,mode,'control'],check=True)
 (E/(a+'-projection.json')).write_bytes((E/'NEL_PAYMENT_VALIDATOR_CURRENT.json').read_bytes())
 r=subprocess.run([sys.executable,str(E/'NEL_kani_run.py'),a,'kani','pool_v1::payment_relation::NEL_payment_validator::payment_validator'],capture_output=True,text=True);print(a,case,mode,r.stdout[-1300:],r.stderr,flush=True)
 if not (E/a/'receipt.json').exists():raise SystemExit('STOP unresolved launch')
 log=(E/a/'stdout.log').read_text()
 if ('VERIFICATION:- SUCCESSFUL' in log)!=(mode=='positive') or 'timed out' in log.lower() or (mode=='negative' and 'Failed Checks:' not in log):raise SystemExit('STOP inspect/split')
