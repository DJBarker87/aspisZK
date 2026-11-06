from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
for a,name,negative,expected in [('NJC_K034','validate_step',True,1),('NJC_K035','validate_step_renamed',False,0),('NJC_K036','validate_end',False,0),('NJC_K037','validate_end',True,1),('NJC_K038','validate_end_renamed',False,0)]:
 r=subprocess.run(['python3',str(E/'NJC_run.py'),a,'kani','verifier::NJC_validate::'+name],env={**os.environ,**({'NJC_INVERT':'1'} if negative else {})});assert r.returncode==expected
 s=(E/a/'stdout.log').read_text();assert 'VERIFICATION:- '+('FAILED' if expected else 'SUCCESSFUL') in s and 'timed out' not in s
 print(a+' matched result',flush=True)
