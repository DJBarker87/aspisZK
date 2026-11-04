from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
jobs=[(100,'NFB_array_finish','NET_bad_argument',1),
(101,'NFB_error_tx1',None,0),(102,'NFB_error_tx1','NET_bad_reply',1),(103,'NFB_error_tx1','NET_bad_frame',1),
(104,'NFB_error_tx2',None,0),(105,'NFB_error_tx2','NET_bad_reply',1),(106,'NFB_error_tx2','NET_bad_frame',1),
(107,'KMX_checks::KMX_ptr_correct',None,0),(108,'KMX_checks::KMX_ptr_wrong',None,1)]
for n,h,f,want in jobs:
 r=subprocess.run([sys.executable,str(E/'NFB_kani.py'),f'NFB_K{n:03}','verifier::NFB_geometry::'+h]+([f] if f else []))
 if r.returncode!=want:raise SystemExit(f'{n} unexpected verdict')
