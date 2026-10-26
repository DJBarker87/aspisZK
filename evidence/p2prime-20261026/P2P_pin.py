"""Read-only source/object comparison; no build, launcher or monitor mutation."""
from pathlib import Path
import subprocess,json,hashlib
P=Path(__file__).resolve().parent;R=P.parents[1]
rs=[json.loads(p.read_text()) for p in sorted(P.glob('P2P_*/receipt.json'))]
assert len(rs)==100
current={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (R/'lean').glob('P2P_*.lean')}
selected={}
for r in rs:
 if r['exit_status']==0:
  for name,record in r['deps_fingerprint']['selected_objects'].items():selected[record['path']]=record
payload=dict(current=current,selected=selected)
script='''from pathlib import Path
import json,hashlib
x=PAYLOAD
B=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
result={'own_modules':[],'selected_objects':[],'mismatches':[]}
for file,h in x['current'].items():
 p=B/file;o=p.with_suffix('.olean');side=Path(str(o)+'.json')
 row=dict(module=p.stem,source_sha256=sha(p),object_sha256=sha(o),object_bytes=o.stat().st_size)
 if row['source_sha256']!=h:result['mismatches'].append(file)
 result['own_modules'].append(row)
for path,old in x['selected'].items():
 p=Path(path);row=dict(path=path,sha256=sha(p),bytes=p.stat().st_size)
 if row['sha256']!=old['sha256']:result['mismatches'].append(path)
 result['selected_objects'].append(row)
print(json.dumps(result,indent=2))
'''.replace('PAYLOAD',repr(payload))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=script,text=True,capture_output=True,check=True)
result=json.loads(r.stdout);assert not result['mismatches'],result['mismatches']
(P/'P2P_HOST_PINS.json').write_text(json.dumps(result,indent=2)+'\n')
print('Pinned',len(result['own_modules']),'own sources/objects and',len(result['selected_objects']),'selected unchanged dependency objects; zero mismatches')
