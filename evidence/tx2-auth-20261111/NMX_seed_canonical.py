"""Read-only sibling import, retaining canonical module owners and source pins."""
from NMX_transport import *
import hashlib
branch='codex/cx-tx2-owned-20261107'
rev=subprocess.check_output(['git','rev-parse',branch],text=True).strip()
expected={}
for i in [*range(42,49),54]:
 a=f'NMS_L{i:03d}'
 d=json.loads(subprocess.check_output(['git','show',rev+':evidence/tx2-owned-20261111/'+a+'/receipt.json']))
 assert d['exit_status']==0
 expected[a]=d['source_hashes']
(E/'NMX_NMS_CANONICAL_RECEIPTS.json').write_text(json.dumps(dict(branch=branch,revision=rev,accepted_sources=expected),indent=1)+'\n')
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,shutil
s=Path('/home/dombarker/project-offloads/codex-cx-tx2-owned-20261111');b=Path({B!r});e={expected!r};sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for a,pins in e.items():
 d=json.loads((s/a/'receipt.json').read_text());assert d['exit_status']==0
 for n,h in pins.items():assert sha(s/n)==h,(a,n)
for source in [*sorted((s/'NMS_RSL_objects').glob('*.olean*')),*sorted((s/'NMS_RSL_objects').glob('*.ir')),*sorted((s/'NMS_objects').glob('NMS_RSLRefine.olean*')),s/'NMS_objects/NMS_RSLRefine.ir']:
 if not source.is_file():continue
 q=b/'NMX_seed/NMS_canonical'/source.name;q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert sha(q)==sha(source)
 else:shutil.copy2(source,q)
 rows.append(dict(source=str(source),copy=str(q),sha256=sha(q),bytes=q.stat().st_size))
print(json.dumps(rows))
''');assert r.returncode==0,r.stderr
(E/'NMX_NMS_CANONICAL_SEED.json').write_text(json.dumps(json.loads(r.stdout),indent=1)+'\n')
p=E/'NMX_ENV.json';env=json.loads(p.read_text());path=B+'/NMX_seed/NMS_canonical'
if path not in env['LEAN_PATH'].split(':'):env['LEAN_PATH']=path+':'+env['LEAN_PATH']
p.write_text(json.dumps(env,indent=1)+'\n')
print('Canonical sibling objects copied with source/receipt pins; shared owners preserved.')
