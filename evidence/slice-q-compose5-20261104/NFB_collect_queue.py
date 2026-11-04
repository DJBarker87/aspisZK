from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
subprocess.run([sys.executable,str(E/'NFB_upload_geometry.py')],check=True)
n=72
for h,mutations in [('NFB_collect_store_tx1',['NET_bad_reply','NET_bad_argument','NET_bad_frame']),('NFB_collect_store_tx2',['NET_bad_reply','NET_bad_argument','NET_bad_frame']),('NFB_collect_finalize_tx1',['NET_bad_argument','NET_bad_frame']),('NFB_collect_finalize_tx2',['NET_bad_argument','NET_bad_frame']),('NFB_array_tx1',['NET_bad_reply','NET_bad_argument','NET_bad_frame']),('NFB_array_tx2',['NET_bad_reply','NET_bad_argument','NET_bad_frame'])]:
 for flags in [[]]+[[f] for f in mutations]:
  r=subprocess.run([sys.executable,str(E/'NFB_kani.py'),f'NFB_K{n:03}','verifier::NFB_geometry::'+h,*flags])
  if r.returncode!=(1 if flags else 0):raise SystemExit(f'{n} unexpected verdict')
  n+=1
assert n==94
for n,h,want in [(94,'KMX_checks::KMX_ptr_correct',0),(95,'KMX_checks::KMX_ptr_wrong',1)]:
 r=subprocess.run([sys.executable,str(E/'NFB_kani.py'),f'NFB_K{n:03}','verifier::NFB_geometry::'+h])
 if r.returncode!=want:raise SystemExit(f'{n} unexpected verdict')
