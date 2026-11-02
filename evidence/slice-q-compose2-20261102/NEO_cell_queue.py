from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
jobs=[(48,'basis_cell','NEO_wrong_cell'),(49,'accumulated_cell',None),(50,'accumulated_cell','NEO_wrong_cell'),(51,'KMX_checks::KMX_ptr_correct',None),(52,'KMX_checks::KMX_ptr_wrong',None)]
for n,name,flag in jobs:
 a=f'NEO_K{n:03}';r=subprocess.run([sys.executable,str(E/'NEO_kani.py'),a,'verifier::NEO_geometry::'+name]+([flag] if flag else []))
 p=E/a/'receipt.json';assert p.exists(),'unresolved submission'
 rc=json.loads(p.read_text());log=(p.parent/'stdout.log').read_text();expected=1 if flag or name.endswith('wrong') else 0
 assert rc['exit_status']==expected and ('VERIFICATION:- FAILED' if expected else 'VERIFICATION:- SUCCESSFUL') in log,'unexpected check; stop and inspect'
 assert 'timed out' not in log.lower(),'no timed-out retry'
