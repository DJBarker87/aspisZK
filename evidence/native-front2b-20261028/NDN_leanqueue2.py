from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for n,t in [(55, 'NDE_Reference14/Types'), (56, 'NDE_Reference14/Funs'), (57, 'NDN_PackedReference'), (58, 'NDN_ArithmeticBounds'), (59, 'NDN_AddWordBridge'), (60, 'NDN_CoordinateBridge'), (61, 'NDN_SerializationBridge'), (62, 'NDN_BindingBoolean'), (63, 'NDN_FieldAppendInduction'), (64, 'NDN_RawProductBridge'), (65, 'NDN_InterpolationBridge')]:
 r=subprocess.run(['python3',str(E/'NDN_run.py'),f'NDN_L{n:03}','lean',t],stdout=(E/f'NDN_L{n:03}-console.log').open('w'),stderr=subprocess.STDOUT)
 if r.returncode:raise SystemExit(r.returncode)
 print('finished',n,flush=True)
