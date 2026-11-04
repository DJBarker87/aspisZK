from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
subprocess.run([sys.executable,str(E/'NFB_upload_geometry.py')],check=True)
def run(n,h,flags,want):
 a=f'NFB_K{n:03}'
 r=subprocess.run([sys.executable,str(E/'NFB_kani.py'),a,'verifier::NFB_geometry::'+h,*flags])
 if r.returncode!=want:raise SystemExit(f'{a}: expected {want}, got {r.returncode}; stop queue')
for n,flags in enumerate([[],['NET_bad_reply'],['NET_bad_argument'],['NET_bad_order']],29):run(n,'NFB_row_arguments',flags,1 if flags else 0)
n=33
for h in ['NFB_resize_tx1','NFB_resize_tx2']:
 for flags in [[],['NET_bad_reply'],['NET_bad_argument'],['NET_bad_frame']]:
  run(n,h,flags,1 if flags else 0);n+=1
run(41,'KMX_checks::KMX_ptr_correct',[],0)
run(42,'KMX_checks::KMX_ptr_wrong',[],1)
