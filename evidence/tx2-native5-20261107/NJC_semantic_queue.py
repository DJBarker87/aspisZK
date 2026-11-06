from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
for a,name,negative,expected in [('NJC_K028','semantic',True,1),('NJC_K029','semantic_renamed',False,0)]:
 r=subprocess.run(['python3',str(E/'NJC_run.py'),a,'kani','verifier::NJC_semantic::'+name],env={**os.environ,**({'NJC_INVERT':'1'} if negative else {})});assert r.returncode==expected
 s=(E/a/'stdout.log').read_text();assert 'VERIFICATION:- '+('FAILED' if expected else 'SUCCESSFUL') in s and 'timed out' not in s
 print(a+' matched result',flush=True)
