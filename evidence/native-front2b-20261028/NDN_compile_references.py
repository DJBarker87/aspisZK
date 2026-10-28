from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
number=15
for n in range(1,21):
 for k in ['Types','Funs']:
  r=subprocess.run(['python3',str(E/'NDN_run.py'),f'NDN_L{number:03}','lean',f'NDN_Reference{n}/{k}'],stdout=(E/f'NDN_L{number:03}-console.log').open('w'),stderr=subprocess.STDOUT)
  if r.returncode:raise SystemExit(r.returncode)
  print('compiled attempt',number,flush=True);number+=1
