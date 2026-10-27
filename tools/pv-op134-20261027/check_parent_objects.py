"""Check cached reference objects against the parent job's latest recorded consumers."""
from pathlib import Path
import json,subprocess,shlex,hashlib
root=Path(__file__).resolve().parents[2];old=root/'evidence/pv-cbmid-20261027';out=root/'evidence/pv-op134-20261027'
expected={}
for p in sorted(old.glob('40[0-9][0-9][0-9].json')):
 r=json.loads(p.read_text())
 if r.get('exit')!=0:continue
 for name,v in r.get('dependency_objects',{}).items():
  if name.startswith('R1Z.PV_CBM_') and 'sha256' in v:expected[name]={'sha256':v['sha256'],'consumer_receipt':str(p.relative_to(root))}
code='''from pathlib import Path
import hashlib,json
base=Path('/home/dombarker/project-offloads/codex-pv-op134-20261027/objects')
r={}
for n in %r:
 p=base/(n.replace('.','/')+'.olean')
 r[n]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'size':p.stat().st_size} if p.is_file() else {'missing':True}
print(json.dumps(r))
'''%list(expected)
actual=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],text=True))
rows={n:dict(expected=expected[n],actual=actual[n],matches=actual[n].get('sha256')==expected[n]['sha256']) for n in expected}
(out/'PARENT-OBJECTS.json').write_text(json.dumps(dict(scope='Latest successful cbmid consumer receipt for each PV_CBM import; focused identity check, not a coherent release replay.',objects=rows),indent=2)+'\n')
assert all(v['matches'] for v in rows.values()),[n for n,v in rows.items() if not v['matches']]
print('PASS',len(rows),'reference objects match parent consumer receipts')
