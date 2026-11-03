from pathlib import Path
import sys,json,subprocess
E=Path(__file__).resolve().parent
jobs=[(17,'KMX_checks::KMX_ptr_correct',None),(18,'KMX_checks::KMX_ptr_wrong',None),(19,'NET_c608',None),(20,'NET_c608','NET_bad_reply'),(21,'NET_c608','NET_bad_frame'),(22,'NET_q608',None),(23,'NET_q608','NET_bad_reply'),(24,'NET_q608','NET_bad_frame')]
for n,h,f in jobs:
 a=f'NET_K{n:03}';r=subprocess.run([sys.executable,str(E/'NET_kani.py'),a,'field::NET_windows::'+h]+([f] if f else []))
 p=E/a/'receipt.json';assert p.exists(),'No terminal receipt; recover only'
 rc=json.loads(p.read_text());text=(p.parent/'stdout.log').read_text();want=int(f is not None or h.endswith('wrong'))
 assert rc['exit_status']==want and ('VERIFICATION:- FAILED' if want else 'VERIFICATION:- SUCCESSFUL') in text,'Unexpected result; isolate before next launch'
 assert 'timed out' not in text.lower()
