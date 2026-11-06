from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
jobs=[('NJC_K058','echeck_step',False,0),('NJC_K059','echeck_step',True,1),('NJC_K060','echeck_step_renamed',False,0),('NJC_K061','compact_step',False,0),('NJC_K062','compact_step',True,1),('NJC_K063','compact_step_renamed',False,0)]
for a,name,negative,expected in jobs:
 r=subprocess.run(['python3',str(E/'NJC_run.py'),a,'kani','verifier::NJC_chunks::'+name],env={**os.environ,**({'NJC_INVERT':'1'} if negative else {})});assert r.returncode==expected,(a,r.returncode)
 s=(E/a/'stdout.log').read_text();assert 'VERIFICATION:- '+('FAILED' if expected else 'SUCCESSFUL') in s and 'timed out' not in s
 print(a+' matched result',flush=True)
