from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
for a,name,flags,expected in [('NJC_K040','accumulator',{'NJC_INVERT':'1'},1),('NJC_K041','accumulator',{'NJC_BAD_ALLOC':'1'},1),('NJC_K042','accumulator_renamed',{},0)]:
 r=subprocess.run(['python3',str(E/'NJC_run.py'),a,'kani','verifier::NJC_vec::'+name],env={**os.environ,**flags});assert r.returncode==expected
 s=(E/a/'stdout.log').read_text();assert 'VERIFICATION:- '+('FAILED' if expected else 'SUCCESSFUL') in s and 'timed out' not in s
 print(a+' matched result',flush=True)
