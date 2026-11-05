from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent;failed=set()
for n,target,deps in[(55,'NHX_KWordLift',[]),(56,'NHX_ProcessReference',[]),(57,'NHX_ProcessPost',['NHX_ProcessReference'])]:
 if any(d in failed for d in deps):continue
 r=subprocess.run(['python3',str(E/'NHX_run.py'),f'NHX_L{n:03}','lean',target])
 if r.returncode:failed.add(target)
