"""Serial own work queue; never repeats a submitted, timed-out or killed job."""
from pathlib import Path
import subprocess,sys,json,time
E=Path(__file__).resolve().parent
# K002 was submitted interactively. Wait only for recovery, never submit it again.
while (E/'NEW_ACTIVE.json').exists():time.sleep(5)
p=E/'NEW_K002/receipt.json'
assert p.exists(),'K002 unresolved: stop queue; recover read-only'
r=json.loads(p.read_text());log=(E/'NEW_K002/stdout.log').read_text()
if r['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in log:
 jobs=[(3,'NET_gather_10',['NET_reserve_only','NET_bad_reply'],1),(4,'NET_gather_12',['NET_reserve_only'],0),(5,'NET_gather_12',['NET_reserve_only','NET_bad_reply'],1)]
else:
 jobs=[]
 print('Reserve attempt excluded; no unchanged reserve rerun',flush=True)
jobs += [(6,'NET_backward_tx2',[],0),(7,'NET_backward_tx2',['NET_bad_reply'],1),(8,'NET_backward_tx2',['NET_bad_argument'],1),(9,'KMX_checks::KMX_ptr_correct',[],0),(10,'KMX_checks::KMX_ptr_wrong',[],1)]
for n,h,flags,want in jobs:
 a=f'NEW_K{n:03}'
 result=subprocess.run([sys.executable,str(E/'NEW_kani.py'),a,'verifier::NEW_geometry::'+h,*flags],capture_output=True,text=True)
 (E/(a+'.driver.log')).write_text(result.stdout+result.stderr)
 p=E/a/'receipt.json';assert p.exists(),'Unresolved submitted attempt; stop and recover read-only'
 rc=json.loads(p.read_text());text=(E/a/'stdout.log').read_text()
 print(a,rc['exit_status'],rc['wall_seconds'],flush=True)
 assert 'timed out' not in text.lower() and rc['exit_status']==want,('new shape requires inspection',a)
 assert ('VERIFICATION:- FAILED' if want else 'VERIFICATION:- SUCCESSFUL') in text
for args in [('NEW_run.py','NEW_L001','NEW_GeometryReverse'),('NEW_job.py','NEW_E001','extract')]:
 r=subprocess.run([sys.executable,str(E/args[0]),*args[1:]],capture_output=True,text=True)
 (E/(args[1]+'.driver.log')).write_text(r.stdout+r.stderr)
 print(args[1],r.returncode,flush=True)
 assert not (E/'NEW_ACTIVE.json').exists(),'Unresolved job; recover read-only'
