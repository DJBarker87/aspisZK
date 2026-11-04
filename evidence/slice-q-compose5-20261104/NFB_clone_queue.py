from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
subprocess.run([sys.executable,str(E/'NFB_upload_geometry.py')],check=True)
for n,h,flags,want in [(43,'NFB_resize_clone',[],0),(44,'NFB_resize_clone',['NET_bad_reply'],1),(45,'KMX_checks::KMX_ptr_correct',[],0),(46,'KMX_checks::KMX_ptr_wrong',[],1)]:
 r=subprocess.run([sys.executable,str(E/'NFB_kani.py'),f'NFB_K{n:03}','verifier::NFB_geometry::'+h,*flags])
 if r.returncode!=want:raise SystemExit(f'{n}: expected {want}, got {r.returncode}')
