from pathlib import Path
import sys,json,subprocess
E=Path(__file__).resolve().parent
jobs=[(25,'NET_wide832',None),(26,'NET_wide832','NET_bad_reply'),(27,'NET_wide832','NET_bad_frame'),(28,'NET_wide_wrong_lengths',None),(29,'NET_wide_wrong_lengths','NET_bad_reply'),(30,'KMX_checks::KMX_ptr_correct',None),(31,'KMX_checks::KMX_ptr_wrong',None)]
for n,h,f in jobs:
 a=f'NET_K{n:03}';subprocess.run([sys.executable,str(E/'NET_kani.py'),a,'field::NET_wide_windows::'+h]+([f] if f else []))
 p=E/a/'receipt.json';assert p.exists(),'No terminal receipt'
 rc=json.loads(p.read_text());text=(p.parent/'stdout.log').read_text();want=int(f is not None or h.endswith('wrong'))
 assert rc['exit_status']==want and ('VERIFICATION:- FAILED' if want else 'VERIFICATION:- SUCCESSFUL') in text,'Unexpected result; isolate before next launch'
 assert 'timed out' not in text.lower()
