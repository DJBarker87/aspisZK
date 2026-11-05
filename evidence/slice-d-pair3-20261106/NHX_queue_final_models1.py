from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent;failed=set()
for n,target,deps in [(41,'NHX_FactoredSuffix',[]),(42,'NHX_FactoredPacket',['NHX_FactoredSuffix']),(43,'NHX_HighReference',[]),(44,'NHX_HighPost',['NHX_HighReference']),(45,'NHX_FinalLoop',[]),(46,'NHX_VecPort',[])]:
 if any(d in failed for d in deps):continue
 r=subprocess.run(['python3',str(E/'NHX_run.py'),f'NHX_L{n:03}','lean',target])
 if r.returncode:failed.add(target)
print('Focused failures:',sorted(failed))
