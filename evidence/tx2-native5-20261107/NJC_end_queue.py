from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
for a,name,negative,expected in [('NJC_K030','weight_end',False,0),('NJC_K031','weight_end',True,1),('NJC_K032','weight_end_renamed',False,0)]:
 r=subprocess.run(['python3',str(E/'NJC_run.py'),a,'kani','verifier::NJC_weight_end::'+name],env={**os.environ,**({'NJC_INVERT':'1'} if negative else {})});assert r.returncode==expected
 s=(E/a/'stdout.log').read_text();assert 'VERIFICATION:- '+('FAILED' if expected else 'SUCCESSFUL') in s and 'timed out' not in s
 print(a+' matched result',flush=True)
