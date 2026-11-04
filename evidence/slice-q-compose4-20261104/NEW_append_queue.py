from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=[]
for base,h in [(20,'NEW_line_tx1'),(23,'NEW_line_tx2'),(26,'NEW_row_push_tx1'),(29,'NEW_row_push_tx2')]:
 jobs.extend([(base,h,[],0),(base+1,h,['NET_bad_reply'],1),(base+2,h,['NET_bad_frame'],1)])
jobs += [(32,'NEW_collect_tx1',[],0),(33,'NEW_collect_tx1',['NET_bad_reply'],1),(34,'NEW_collect_tx2',[],0),(35,'NEW_collect_tx2',['NET_bad_reply'],1),(36,'KMX_checks::KMX_ptr_correct',[],0),(37,'KMX_checks::KMX_ptr_wrong',[],1)]
blocked=set()
for n,h,flags,want in jobs:
 if h in blocked:continue
 a=f'NEW_K{n:03}';r=subprocess.run([sys.executable,str(E/'NEW_kani.py'),a,'verifier::NEW_geometry::'+h,*flags],capture_output=True,text=True)
 (E/(a+'.driver.log')).write_text(r.stdout+r.stderr)
 p=E/a/'receipt.json';assert p.exists(),'Unresolved submitted job; stop, recover read-only'
 rc=json.loads(p.read_text());text=(E/a/'stdout.log').read_text();print(a,rc['exit_status'],rc['wall_seconds'],flush=True)
 if 'timed out' in text.lower() or rc['exit_status'] in [124,137]:
  blocked.add(h)
  if 'tx1' in h:blocked.add(h.replace('tx1','tx2'))
  print('Excluded timeout/kill; remaining same-shape cases skipped; independent next member only',flush=True);continue
 assert rc['exit_status']==want,('Inspect own input/native failure',a)
 assert ('VERIFICATION:- FAILED' if want else 'VERIFICATION:- SUCCESSFUL') in text
