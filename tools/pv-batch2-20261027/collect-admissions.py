from pathlib import Path
import subprocess,json
E=Path('evidence/pv-batch2-20261027');t=json.loads((E/'TALLY.json').read_text());ids=[a['id'] for a in t['attempts']]
code='''from pathlib import Path
import json
H=Path('/home/dombarker/project-offloads/codex-pv-batch2-20261027/candidate')
out={}
for n in IDS:
 d=H/('lean-'+str(n))
 for name in ['reservation.json','reservation.log','admission-barrier.json','command.json','scope.log']:
  p=d/name
  if p.exists():out[str(p.relative_to(H))]=p.read_text()
print(json.dumps(out))
'''.replace('IDS',repr(ids))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
for rel,text in json.loads(r.stdout).items():
 p=E/'candidate'/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text)
print('Collected admission/command records for',len(ids),'assigned IDs')
