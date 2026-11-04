from pathlib import Path
import sys,json,subprocess
E=Path(__file__).resolve().parent
jobs=[(32,'NET_field_valid',None),(33,'NET_field_valid','NET_bad_reply'),(34,'NET_field_valid','NET_bad_frame'),(35,'NET_field_rejected',None),(36,'NET_field_rejected','NET_bad_option'),(37,'KMX_checks::KMX_ptr_correct',None),(38,'KMX_checks::KMX_ptr_wrong',None)]
for n,h,f in jobs:
 a=f'NET_K{n:03}';subprocess.run([sys.executable,str(E/'NET_kani.py'),a,'verifier::NET_fields::'+h]+([f] if f else []))
 p=E/a/'receipt.json';assert p.exists(),'No terminal receipt; recover only'
 rc=json.loads(p.read_text());text=(p.parent/'stdout.log').read_text();want=int(f is not None or h.endswith('wrong'))
 assert rc['exit_status']==want and ('VERIFICATION:- FAILED' if want else 'VERIFICATION:- SUCCESSFUL') in text,'Unexpected result; isolate before next launch'
 assert 'timed out' not in text.lower()
