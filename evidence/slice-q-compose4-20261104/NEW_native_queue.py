"""Changed scratch feature input; matched controls with original harness names."""
from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
assert not (E/'NEW_ACTIVE.json').exists()
jobs=[(11,'NET_gather_10',['NET_reserve_only'],0),(12,'NET_gather_10',['NET_reserve_only','NET_bad_reply'],1),(13,'NET_gather_12',['NET_reserve_only'],0),(14,'NET_gather_12',['NET_reserve_only','NET_bad_reply'],1),(15,'NET_backward_tx2',[],0),(16,'NET_backward_tx2',['NET_bad_reply'],1),(17,'NET_backward_tx2',['NET_bad_argument'],1),(18,'KMX_checks::KMX_ptr_correct',[],0),(19,'KMX_checks::KMX_ptr_wrong',[],1)]
for n,h,flags,want in jobs:
 a=f'NEW_K{n:03}'
 result=subprocess.run([sys.executable,str(E/'NEW_kani.py'),a,'verifier::NEW_geometry::'+h,*flags],capture_output=True,text=True)
 (E/(a+'.driver.log')).write_text(result.stdout+result.stderr)
 p=E/a/'receipt.json';assert p.exists(),'Unresolved submitted attempt; recover read-only'
 rc=json.loads(p.read_text());text=(E/a/'stdout.log').read_text()
 print(a,rc['exit_status'],rc['wall_seconds'],flush=True)
 if 'timed out' in text.lower() or rc['exit_status'] in [124,137]:
  print('Excluded timeout/kill; no rerun. Isolate and inspect before further related cases.',flush=True);break
 assert rc['exit_status']==want,('inspect unexpected failure',a)
 assert ('VERIFICATION:- FAILED' if want else 'VERIFICATION:- SUCCESSFUL') in text
