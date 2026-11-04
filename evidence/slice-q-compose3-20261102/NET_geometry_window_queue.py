from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
subprocess.run([sys.executable,str(E/'NET_upload_geometry_window.py')],check=True)
jobs=[(91,'NET_gather_10',['NET_reserve_only'],0),(92,'NET_gather_10',['NET_reserve_only','NET_bad_reply'],1),(93,'NET_gather_12',['NET_reserve_only'],0),(94,'NET_gather_12',['NET_reserve_only','NET_bad_reply'],1),(95,'NET_gather_10',['NET_one_push'],0),(96,'NET_gather_10',['NET_one_push','NET_bad_reply'],1),(97,'NET_gather_12',['NET_one_push'],0),(98,'NET_gather_12',['NET_one_push','NET_bad_reply'],1),(99,'KMX_checks::KMX_ptr_correct',[],0),(100,'KMX_checks::KMX_ptr_wrong',[],1)]
for n,h,flags,want in jobs:
 a=f'NET_K{n:03}';subprocess.run([sys.executable,str(E/'NET_kani.py'),a,'verifier::NET_geometry::'+h,*flags])
 r=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text()
 assert 'timed out' not in log.lower(),'Excluded timeout; move to independent shape'
 assert r['exit_status']==want and ('VERIFICATION:- FAILED' if want else 'VERIFICATION:- SUCCESSFUL') in log
