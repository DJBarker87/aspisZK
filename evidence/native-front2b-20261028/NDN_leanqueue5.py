from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for n,t in [(76, 'NDN_RequestTagFinding'), (77, 'NDN_EqualityLoop'), (78, 'NDN_ChunkGeometry'), (79, 'NDN_InterpolationPrefix')]:
 r=subprocess.run(['python3',str(E/'NDN_run.py'),f'NDN_L{n:03}','lean',t],stdout=(E/f'NDN_L{n:03}-console.log').open('w'),stderr=subprocess.STDOUT)
 if r.returncode:raise SystemExit(r.returncode)
 print('finished',n,flush=True)
