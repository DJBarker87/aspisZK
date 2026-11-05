from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent;failed=set()
for n,target,deps in [(20,'NHX_FactoredCut',[]),(21,'NHX_FactoredSuffix',['NHX_FactoredCut']),(22,'NHX_HighDomain',[]),(23,'NHX_Inspect',['NHX_HighDomain']),(24,'NHX_ProcessKind',[]),(25,'NHX_FinalFold',[]),(26,'NHX_Powers7Edge',[]),(27,'NHX_FinalLoop',['NHX_FinalFold','NHX_Powers7Edge'])]:
 if any(d in failed for d in deps):continue
 r=subprocess.run(['python3',str(E/'NHX_run.py'),f'NHX_L{n:03}','lean',target])
 if r.returncode:failed.add(target)
print('Failed focused targets:',sorted(failed))
