"""Use the final Kani slot for a changed concrete control of K02, never a rerun."""
from pathlib import Path
import json,subprocess,time,sys,shlex
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-kstub-20261028';D='/home/dombarker/project-offloads/codex-pv-kstub-20261028';H='dombarker@100.108.41.90'
def remote(args,code=None):
 for attempt in range(11):
  q=subprocess.run(['ssh',H,shlex.join(args)],input=code,text=True,capture_output=True)
  if q.returncode!=255:break
  with (E/'final-control-transport.jsonl').open('a') as f:f.write(json.dumps(dict(exit=255,attempt=attempt,time=time.time(),stderr=q.stderr))+'\n')
  if attempt<10:time.sleep(60)
 if q.returncode:raise RuntimeError(q.stderr or q.stdout)
 return q.stdout
assert len(list(E.glob('K??/receipt.json')))==29,'Finish the serial queue first'
assert not (E/'K30/receipt.json').exists()
code='''from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-kstub-20261028');p=D/'cb/lib.rs';s=p.read_text();a=s.index('fn path_join8_negative()');b=s.index('\\n    }',a)+6;old=s[a:b]
new=old.replace('let a:[u8;8]=kani::any();let b:[u8;8]=kani::any();','let a:[u8;8]=[65;8];let b:[u8;8]=[66;8];').replace('let n:usize=kani::any();let m:usize=kani::any();','let n:usize=8;let m:usize=8;')
assert new!=old
p.write_text(s[:a]+new+s[b:]);record=dict(before=old,after=new,before_sha256=hashlib.sha256(old.encode()).hexdigest(),after_sha256=hashlib.sha256(new.encode()).hexdigest(),reason='Concrete changing-output control replaces timed-out symbolic control K03; same KMX patch, calls, bound and intended false equality')
(D/'K30-change.json').write_text(json.dumps(record,indent=2));print(json.dumps(record))
'''
(E/'K30-change.json').write_text(remote(['python3','-'],code))
t=json.loads((E/'K03-target.json').read_text());(E/'K30-target.json').write_text(json.dumps(t,indent=2)+'\n')
remote(['python3',D+'/freeze-inputs.py','K30','cb'])
for k in range(11):
 q=subprocess.run([sys.executable,str(R/'tools/pv-kstub-20261028/scope.py'),'K30','Kani',*t['command']])
 if q.returncode==79:time.sleep(60);continue
 if q.returncode!=78:break
 if k<10:time.sleep(180)
f=E/'K30/receipt.json'
if not f.exists():raise RuntimeError('K30 unresolved; recover, never resubmit')
r=json.loads(f.read_text());log=f.with_name('output.log').read_text();status='TIMEOUT' if r['exit']==124 else 'PASS' if 'VERIFICATION:- SUCCESSFUL' in log else 'FAIL' if 'VERIFICATION:- FAILED' in log else 'ERROR'
out={k:v for k,v in t.items() if k!='command'};out.update(run='K30',status=status,receipt=str(f.relative_to(R)),source_change='K30-change.json');(E/'K30-result.json').write_text(json.dumps(out,indent=2)+'\n')
assert status=='FAIL','Review final control before proceeding'
