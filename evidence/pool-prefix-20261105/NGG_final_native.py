from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
jobs=[(114,'NGG_leaf.py','count18','positive','pair_forest::NGG_Leaf::association'),(115,'NGG_leaf.py','count18','negative','pair_forest::NGG_Leaf::association'),(116,'NGG_marker_native.py','predicate','positive','nullifier::NGG_Marker::association'),(117,'NGG_marker_native.py','predicate','negative','nullifier::NGG_Marker::association'),(118,'NGG_marker_native.py','metadata','positive','nullifier::NGG_Marker::association'),(119,'NGG_marker_native.py','metadata','negative','nullifier::NGG_Marker::association')]
for n,gen,kind,mode,target in jobs:
 subprocess.run(['python3',str(E/gen),kind,mode],check=True)
 r=subprocess.run(['python3',str(E/'NGG_kani_run.py'),f'NGG_K{n:03}',target])
 if not (E/f'NGG_K{n:03}/receipt.json').exists():raise SystemExit('unresolved attempt')
