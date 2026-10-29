from pathlib import Path
import sys,subprocess,json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-diag10-20261029')
m,start,plan,*rest=sys.argv[1:];start=int(start);cs=json.loads((D/plan).read_text())[m]
if rest:cs=cs[int(rest[0]):]
for n,s in enumerate(cs,start):
 p=D/'sources'/(m.replace('.','/')+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
 # Fail closed on any previously rejected identical source, irrespective of ID.
 digest=hashlib.sha256(s.encode()).hexdigest()
 for old in D.glob('lean*-receipt.json'):
  r=json.loads(old.read_text())
  assert not(r.get('exit')!=0 and r.get('source_sha256')==digest),'unchanged failed source'
 r=subprocess.run(['python3',str(D/'run.py'),'lean'+str(n),'lean',str(n),m])
 if r.returncode:sys.exit(r.returncode)
