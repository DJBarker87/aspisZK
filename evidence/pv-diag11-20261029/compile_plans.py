from pathlib import Path
import sys,json,subprocess,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-diag11-20261029')
plans=json.loads((D/'plans.json').read_text())
start=int(sys.argv[1]); names=sys.argv[2:]
for spec in names:
 m,_,off=spec.partition(":")
 for s in plans[m][int(off or 0):]:
  p=D/'sources'/(m+'.lean');p.write_text(s)
  digest=hashlib.sha256(s.encode()).hexdigest()
  for old in D.glob('lean*-receipt.json'):
   r=json.loads(old.read_text())
   assert not(r['exit']!=0 and r.get('source_sha256')==digest),'unchanged failed source'
  assert start<67097
  r=subprocess.run(['python3',str(D/'run.py'),'lean'+str(start),'lean',str(start),m])
  start+=1
  if r.returncode:sys.exit(r.returncode)
print('NEXT',start)
