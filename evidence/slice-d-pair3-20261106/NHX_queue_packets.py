from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent;failed=set()
for n,target,deps in [(36,'NHX_FactoredSuffix',[]),(37,'NHX_FactoredPacket',['NHX_FactoredSuffix']),(38,'NHX_HighReference',[]),(39,'NHX_HighPost',['NHX_HighReference']),(40,'NHX_FinalLoop',[])]:
 if any(d in failed for d in deps):continue
 r=subprocess.run(['python3',str(E/'NHX_run.py'),f'NHX_L{n:03}','lean',target])
 if r.returncode:failed.add(target)
print('Focused failures:',sorted(failed))
