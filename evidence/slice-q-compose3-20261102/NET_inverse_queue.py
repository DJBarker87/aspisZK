from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=[(2,'NET_cm_result_log_frame','NET_bad_reply'),(3,'NET_cm_result_log_frame','NET_bad_argument'),(4,'NET_cm_result_log_frame','NET_bad_frame'),(5,'NET_copy_positive',None),(6,'NET_copy_negative',None)]
for n,h,f in jobs:
 a=f'NET_K{n:03}'
 r=subprocess.run([sys.executable,str(E/'NET_kani.py'),a,'field::NET_inverse::'+h]+([f] if f else []))
 p=E/a/'receipt.json'
 assert p.exists(),'No terminal receipt; recover only'
 rc=json.loads(p.read_text());log=(p.parent/'stdout.log').read_text();want=int(f is not None or h=='NET_copy_negative')
 assert rc['exit_status']==want and ('VERIFICATION:- FAILED' if want else 'VERIFICATION:- SUCCESSFUL') in log,'Unexpected result; inspect before next launch'
 assert 'timed out' not in log.lower()
