from pathlib import Path
import os,subprocess,json
E=Path(__file__).resolve().parent
jobs=[(20,'low_lhs',True)]+[(21+2*i+j,n,bool(j)) for i,n in enumerate(['low_rhs','low_order','low_scalar','low_scale','low_frame']) for j in range(2)]
for i,name,control in jobs:
 env=dict(os.environ)
 if control:env.update(NIG_INVERT='1',NIG_NATIVE_CFG='NIG_corrupt')
 r=subprocess.run(['python3',str(E/'NIG_run.py'),f'NIG_K{i:03}','kani','weights::NIG_stages::'+name],env=env)
 receipt=json.loads((E/f'NIG_K{i:03}/receipt.json').read_text());log=(E/f'NIG_K{i:03}/stdout.log').read_text()
 if r.returncode!=(1 if control else 0) or 'timed out' in log.lower() or 'unwinding failures' in log or ('VERIFICATION:- FAILED' if control else 'VERIFICATION:- SUCCESSFUL')not in log:raise SystemExit('Review failed stage '+str(i))
