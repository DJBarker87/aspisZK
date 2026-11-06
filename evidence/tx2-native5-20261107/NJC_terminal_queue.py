from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
jobs=[(72,'option_e',None,0),(73,'option_e','NJC_INVERT',1),(74,'option_e','NJC_BAD_ERROR',1),(75,'option_e_renamed',None,0),(76,'map_allocation',None,0),(77,'map_allocation','NJC_INVERT',1),(78,'map_allocation','NJC_BAD_ERROR',1),(79,'map_allocation_renamed',None,0),(80,'header_predicate',None,0)]
for n,name,negative,expected in jobs:
 a=f'NJC_K{n:03d}';r=subprocess.run(['python3',str(E/'NJC_run.py'),a,'kani','verifier::candidate::NJC_terminal::'+name],env={**os.environ,**({negative:'1'} if negative else {})});assert r.returncode==expected,(a,r.returncode)
 s=(E/a/'stdout.log').read_text();assert 'VERIFICATION:- '+('FAILED' if expected else 'SUCCESSFUL') in s and 'timed out' not in s
 print(a+' matched result',flush=True)
