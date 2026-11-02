from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
jobs=[(73,'field_ok',None),(74,'field_ok','NEO_wrong_field'),(75,'field_bad',None),(76,'field_bad','NEO_wrong_badfield'),(77,'geometry_empty',None),(78,'geometry_empty','NEO_wrong_empty'),(79,'KMX_checks::KMX_ptr_correct',None),(80,'KMX_checks::KMX_ptr_wrong',None)]
for n,name,flag in jobs:
 a=f'NEO_K{n:03}';subprocess.run([sys.executable,str(E/'NEO_kani.py'),a,'verifier::NEO_geometry::'+name]+([flag] if flag else []))
 p=E/a/'receipt.json';assert p.exists(),'unresolved submission'
 rc=json.loads(p.read_text());log=(p.parent/'stdout.log').read_text();expected=1 if flag or name.endswith('wrong') else 0
 assert rc['exit_status']==expected,'unexpected check; stop and inspect'
 assert 'timed out' not in log.lower(),'no timed-out retry'
