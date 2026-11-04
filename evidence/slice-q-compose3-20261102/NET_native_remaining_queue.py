from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
assert not (E/'NET_ACTIVE.json').exists()
subprocess.run([sys.executable,str(E/'NET_upload_geometry.py')],check=True)
jobs=[(85,'NET_prefix_meta::NET_prefix_allocation',None),(86,'NET_prefix_meta::NET_prefix_allocation','NET_bad_reply'),(87,'NET_prefix_meta::NET_prefix_empty',None),(88,'NET_prefix_meta::NET_prefix_empty','NET_bad_reply'),(89,'NET_geometry::NET_gather_10',None),(90,'NET_geometry::NET_gather_10','NET_bad_reply'),(91,'NET_geometry::NET_gather_12',None),(92,'NET_geometry::NET_gather_12','NET_bad_reply'),(93,'NET_geometry::NET_gather_22',None),(94,'NET_geometry::NET_gather_22','NET_bad_reply'),(95,'NET_geometry::NET_gather_rejected',None),(96,'NET_geometry::NET_gather_rejected','NET_bad_option'),(97,'NET_geometry::NET_backward_tx1',None),(98,'NET_geometry::NET_backward_tx1','NET_bad_reply'),(99,'NET_geometry::NET_backward_tx2',None),(100,'NET_geometry::NET_backward_tx2','NET_bad_reply'),(101,'NET_geometry::KMX_checks::KMX_ptr_correct',None),(102,'NET_geometry::KMX_checks::KMX_ptr_wrong',None)]
for n,h,f in jobs:
 a=f'NET_K{n:03}';subprocess.run([sys.executable,str(E/'NET_kani.py'),a,'verifier::'+h]+([f] if f else []))
 r=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text();bad=bool(f or h.endswith('wrong'))
 assert r['exit_status']==int(bad) and ('VERIFICATION:- FAILED' if bad else 'VERIFICATION:- SUCCESSFUL') in log,'Stop unexpected shape; isolate before next attempt'
 assert 'timed out' not in log.lower()
