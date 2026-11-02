from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
jobs=[(54,'c_window','NEO_wrong_window'),(55,'q_window',None),(56,'q_window','NEO_wrong_window'),(57,'wide_window',None),(58,'wide_window','NEO_wrong_window'),(59,'KMX_checks::KMX_ptr_correct',None),(60,'KMX_checks::KMX_ptr_wrong',None)]
for n,name,flag in jobs:
 a=f'NEO_K{n:03}';subprocess.run([sys.executable,str(E/'NEO_kani.py'),a,'field::NEO_parsers::'+name]+([flag] if flag else []))
 p=E/a/'receipt.json';assert p.exists(),'unresolved submission'
 rc=json.loads(p.read_text());log=(p.parent/'stdout.log').read_text();expected=1 if flag or name.endswith('wrong') else 0
 assert rc['exit_status']==expected and ('VERIFICATION:- FAILED' if expected else 'VERIFICATION:- SUCCESSFUL') in log,'unexpected check; stop and inspect'
 assert 'timed out' not in log.lower(),'no timed-out retry'
