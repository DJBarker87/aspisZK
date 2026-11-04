from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
subprocess.run([sys.executable,str(E/'NET_upload_geometry_split.py')],check=True)
jobs=[(90,'NET_gather_10',['NET_only_new'],0),(91,'NET_gather_10',['NET_only_new','NET_bad_reply'],1),(92,'NET_gather_10',['NET_only_frame'],0),(93,'NET_gather_10',['NET_only_frame','NET_bad_frame'],1),(94,'NET_gather_12',['NET_only_new'],0),(95,'NET_gather_12',['NET_only_new','NET_bad_reply'],1),(96,'NET_gather_12',['NET_only_frame'],0),(97,'NET_gather_12',['NET_only_frame','NET_bad_frame'],1),(98,'KMX_checks::KMX_ptr_correct',[],0),(99,'KMX_checks::KMX_ptr_wrong',[],1),(100,'NET_gather_10',['NET_only_frame','NET_bad_argument'],1)]
for n,h,flags,want in jobs:
 a=f'NET_K{n:03}';subprocess.run([sys.executable,str(E/'NET_kani.py'),a,'verifier::NET_geometry::'+h,*flags])
 r=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text()
 assert 'timed out' not in log.lower(),'Excluded timeout; move to independent shape, never rerun unchanged'
 assert r['exit_status']==want and ('VERIFICATION:- FAILED' if want else 'VERIFICATION:- SUCCESSFUL') in log
