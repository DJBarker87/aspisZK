from pathlib import Path
import os,subprocess,json
E=Path(__file__).resolve().parent
jobs=[(10,'common_lhs',True),(11,'common_rhs',False),(12,'common_rhs',True),(13,'common_count',False),(14,'common_count',True),(15,'common_frame',False),(16,'common_frame',True)]
for i,name,control in jobs:
 env=dict(os.environ)
 if control:env.update(NIG_INVERT='1',NIG_NATIVE_CFG='NIG_corrupt')
 r=subprocess.run(['python3',str(E/'NIG_run.py'),f'NIG_K{i:03}','kani','weights::NIG_stages::'+name],env=env)
 receipt=json.loads((E/f'NIG_K{i:03}/receipt.json').read_text());log=(E/f'NIG_K{i:03}/stdout.log').read_text()
 if r.returncode!=(1 if control else 0) or 'timed out' in log.lower() or 'unwinding failures' in log or ('VERIFICATION:- FAILED' if control else 'VERIFICATION:- SUCCESSFUL')not in log:raise SystemExit('Review failed stage '+str(i))
