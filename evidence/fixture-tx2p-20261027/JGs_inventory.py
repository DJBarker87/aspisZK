from pathlib import Path
import subprocess,json,hashlib
P=Path(__file__).resolve().parent;R=P.parents[1];B='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'
v=json.loads((P/'JGs_VALIDATION.json').read_text());names=sorted(v)
remote='''from pathlib import Path
import hashlib,json
B=Path(%r);names=%r
rows={}
for name in names:
 p=B/name;module=p.stem
 row={'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'objects':{}}
 for suffix in ['.olean','.olean.server','.olean.private','.ir']:
  q=B/(module+suffix)
  if q.exists():row['objects'][q.name]={'sha256':hashlib.sha256(q.read_bytes()).hexdigest(),'bytes':q.stat().st_size}
 rows[name]=row
print(json.dumps(rows))
'''%(B,names)
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=remote,text=True,capture_output=True,check=True);rows=json.loads(r.stdout)
recorded={}
for p in P.glob('JGs_TX2_[0-9][0-9][0-9]/receipt.json'):
 d=json.loads(p.read_text())
 for key,record in d.get('deps_fingerprint',{}).get('selected_objects',{}).items():
  if Path(key).name.startswith('JGs_'):recorded.setdefault(Path(key).name,set()).add(record['sha256'])
for name,row in rows.items():
 assert row['source_sha256']==v[name]['sha256'],name
 assert name.removesuffix('.lean')+'.olean' in row['objects'],name
 for obj,entry in row['objects'].items():
  if obj in recorded:assert entry['sha256'] in recorded[obj],obj
(P/'JGs_SELECTED_OBJECTS.json').write_text(json.dumps(rows,indent=2)+'\n')
print('Own checked source/object companions pinned:',len(rows))
