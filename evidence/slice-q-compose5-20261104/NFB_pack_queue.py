from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent

def run(n,h,flags,want):
 a=f'NFB_K{n:03}'
 r=subprocess.run([sys.executable,str(E/'NFB_kani.py'),a,'verifier::NFB_geometry::'+h,*flags])
 if r.returncode!=want:raise SystemExit(f'{a}: expected {want}, got {r.returncode}; stop queue')
subprocess.run([sys.executable,str(E/'NFB_restore_copy_config.py')],check=True)
run(13,'KMX_checks::KMX_ptr_correct',[],0)
run(14,'KMX_checks::KMX_ptr_wrong',[],1)
subprocess.run([sys.executable,str(E/'NFB_upload_geometry.py')],check=True)
run(15,'NFB_range_guard',[],0)
run(16,'NFB_range_guard',['NET_bad_reply'],1)
n=17
for h in ['NFB_pack_tx1','NFB_pack_tx2']:
 for flags in [[],['NET_bad_reply'],['NET_bad_argument'],['NET_bad_frame'],['NFB_wrong_wrapper']]:
  run(n,h,flags,1 if flags else 0);n+=1
run(27,'KMX_checks::KMX_ptr_correct',[],0)
run(28,'KMX_checks::KMX_ptr_wrong',[],1)
