from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
subprocess.run([sys.executable,str(E/'NFB_upload_geometry.py')],check=True)
n=47
for h in ['NFB_inverse_initial_tx1','NFB_inverse_initial_tx2']:
 for flags in [[],['NET_bad_reply'],['NET_bad_argument'],['NET_bad_frame']]:
  r=subprocess.run([sys.executable,str(E/'NFB_kani.py'),f'NFB_K{n:03}','verifier::NFB_geometry::'+h,*flags])
  if r.returncode!=(1 if flags else 0):raise SystemExit(f'{n} unexpected verdict')
  n+=1
for n,h,want in [(55,'KMX_checks::KMX_ptr_correct',0),(56,'KMX_checks::KMX_ptr_wrong',1)]:
 r=subprocess.run([sys.executable,str(E/'NFB_kani.py'),f'NFB_K{n:03}','verifier::NFB_geometry::'+h])
 if r.returncode!=want:raise SystemExit(f'{n} unexpected verdict')
