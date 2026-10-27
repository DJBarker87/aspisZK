"""Prepare pinned differential sources/runners; never launch timing."""
from pathlib import Path
import subprocess,json,hashlib
P=Path(__file__).resolve().parent
D='/home/dombarker/project-offloads/codex-pv-integ4-20261027';H='dombarker@100.108.41.90'
def remote(code):subprocess.run(['ssh',H,'python3','-'],input=code,text=True,check=True)
remote(f'''from pathlib import Path
import subprocess,json
D=Path({D!r});O=D/'upload-resume';O.mkdir()
r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/reservation.py',str(O/'admission.json')],stdout=open(O/'output.log','w'),stderr=subprocess.STDOUT)
assert r.returncode==0 and json.loads((O/'admission.json').read_text())['allowed']
(D/'combined/baseline/source').mkdir(parents=True)
(D/'combined/candidate').mkdir()
(D/'combined/candidate/source').symlink_to(D/'source',target_is_directory=True)
''')
a=subprocess.Popen(['git','archive','c57a344726','Cargo.toml','Cargo.lock','.cargo','crates','programs','audit','xtask','tools','docs/research/v8-r0-zk-20261009/refine','docs/research/v8-r0-zk-20261009/c3','docs/research/v8-r0-zk-20261009/z4'],stdout=subprocess.PIPE)
r=subprocess.run(['ssh',H,f'tar xf - -C {D}/combined/baseline/source'],stdin=a.stdout);assert r.returncode==0 and a.wait()==0
payload={}
for side,rev in [('baseline','c57a344726745387efb38d1571d885c69ce829ee'),('candidate','03905a52594fadc50a1c00ab3f240a79632e8ffd')]:
 for name in ['native.py','capped.py','capped-template.py','reservation.py']:
  payload[side+'/'+name]=(P/name).read_text().replace(D,D+'/combined/'+side)
 payload[side+'/source-revision.txt']=rev+'\n'
for src,dst in [('combined-corpus.py','corpus.py'),('combined-timing.py','timing.py')]:payload[dst]=(P/src).read_text()
for name in ['run_host.py','capped.py','capped-template.py']:payload[name]=(P/name).read_text().replace(D,D+'/combined')
payload['source-revision.txt']='03905a52594fadc50a1c00ab3f240a79632e8ffd\n'
remote(f'''from pathlib import Path
import json,hashlib
D=Path({(D+'/combined')!r});payload={payload!r}
for name,body in payload.items():
 p=D/name;assert not p.exists();p.write_text(body)
(D/'quiet-preflight.py').write_bytes(Path('/home/dombarker/project-offloads/codex-pv-op223-20261027/quiet-preflight.py').read_bytes())
(D/'runner-pins.json').write_text(json.dumps({{n:hashlib.sha256(s.encode()).hexdigest() for n,s in payload.items()}},indent=2))
''')
