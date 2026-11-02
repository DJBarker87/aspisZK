from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
plan=[(30,'first','positive','pool_v1::pair_forest_accounts::NEL_first::first'),(31,'first','negative','pool_v1::pair_forest_accounts::NEL_first::first'),(32,'common_validator','positive','pool_v1::payment_relation::NEL_common_validator::common_validator'),(33,'common_validator','negative','pool_v1::payment_relation::NEL_common_validator::common_validator')]
for n,case,mode,h in plan:
 a=f'NEL_K{n:03}';subprocess.run([sys.executable,str(E/('NEL_prepare_'+case+'.py')),mode],check=True)
 r=subprocess.run([sys.executable,str(E/'NEL_kani_run.py'),a,'kani',h],text=True,capture_output=True);print(a,r.stdout[-1200:],r.stderr,flush=True)
 if not (E/a/'receipt.json').exists():raise SystemExit('STOP unresolved launch')
 log=(E/a/'stdout.log').read_text()
 if ('VERIFICATION:- SUCCESSFUL' in log)!=(mode=='positive') or 'timed out' in log.lower() or (mode=='negative' and 'Failed Checks:' not in log):raise SystemExit('STOP inspect/split this case')
