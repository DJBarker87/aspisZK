from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=[(3,'NFB_zero_iteration_all',['NET_bad_reply'],1),(4,'NFB_zero_iteration_all',['NET_bad_argument'],1),(5,'NFB_zero_iteration_all',['NET_bad_frame'],1),(6,'NFB_zero_iteration_all',['NFB_wrong_getter'],1),(7,'NFB_zero_iteration_all',['NFB_wrong_wrapper'],1),(8,'NFB_zero_callback',[],0),(9,'NFB_zero_callback',['NET_bad_reply'],1),(10,'NFB_zero_readonly_world',[],0),(11,'NFB_zero_readonly_world',['NET_bad_frame'],1)]
for n,h,flags,want in jobs:
 a=f'NFB_K{n:03}'
 r=subprocess.run([sys.executable,str(E/'NFB_kani.py'),a,'verifier::NFB_geometry::'+h,*flags])
 if r.returncode!=want:raise SystemExit(f'{a}: expected {want}, got {r.returncode}; stop queue')
