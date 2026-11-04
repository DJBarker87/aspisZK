from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
subprocess.run([sys.executable,str(E/'NFB_upload_geometry.py')],check=True)
n=57
for h in ['NFB_query_next_tx1','NFB_query_next_tx2']:
 for flags in [[],['NET_bad_reply'],['NET_bad_argument'],['NFB_wrong_getter'],['NET_bad_frame']]:
  r=subprocess.run([sys.executable,str(E/'NFB_kani.py'),f'NFB_K{n:03}','verifier::NFB_geometry::'+h,*flags])
  if r.returncode!=(1 if flags else 0):raise SystemExit(f'{n} unexpected verdict')
  n+=1
for n,h,want in [(67,'KMX_checks::KMX_ptr_correct',0),(68,'KMX_checks::KMX_ptr_wrong',1)]:
 r=subprocess.run([sys.executable,str(E/'NFB_kani.py'),f'NFB_K{n:03}','verifier::NFB_geometry::'+h])
 if r.returncode!=want:raise SystemExit(f'{n} unexpected verdict')
