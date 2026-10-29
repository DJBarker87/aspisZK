from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for n,t in [(66, 'NDN_ArithmeticBounds'), (67, 'NDN_SerializationBridge'), (68, 'NDN_BindingBoolean'), (69, 'NDN_FieldAppendInduction'), (70, 'NDN_RawProductBridge'), (71, 'NDN_InterpolationBridge')]:
 r=subprocess.run(['python3',str(E/'NDN_run.py'),f'NDN_L{n:03}','lean',t],stdout=(E/f'NDN_L{n:03}-console.log').open('w'),stderr=subprocess.STDOUT)
 if r.returncode:raise SystemExit(r.returncode)
 print('finished',n,flush=True)
