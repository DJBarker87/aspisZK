from pathlib import Path
import json,sys,subprocess
E=Path(__file__).resolve().parent
jobs=[(9,'NET_try_result_log_frame',None),(10,'NET_try_result_log_frame','NET_bad_reply'),(11,'NET_try_result_log_frame','NET_bad_argument'),(12,'NET_try_result_log_frame','NET_bad_frame'),(13,'NET_inv_success',None),(14,'NET_inv_success','NET_bad_reply'),(15,'NET_inv_zero',None),(16,'NET_inv_zero','NET_bad_option')]
for n,h,f in jobs:
 a=f'NET_K{n:03}';r=subprocess.run([sys.executable,str(E/'NET_kani.py'),a,'field::NET_qinverse::'+h]+([f] if f else []))
 p=E/a/'receipt.json';assert p.exists(),'No terminal receipt'
 rc=json.loads(p.read_text());text=(p.parent/'stdout.log').read_text();want=int(f is not None)
 assert rc['exit_status']==want and ('VERIFICATION:- FAILED' if want else 'VERIFICATION:- SUCCESSFUL') in text,'Unexpected result; inspect before next launch'
 assert 'timed out' not in text.lower()
