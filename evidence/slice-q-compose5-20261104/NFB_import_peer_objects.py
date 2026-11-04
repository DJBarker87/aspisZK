from NFB_remote import *
import hashlib,json
assert not (E/'NFB_ACTIVE.json').exists()
a='NFB_PEER_OBJECTS';admit(a)
rows=json.loads((E/'NFB_peer_inputs/NFA_OBJECT_EXPORTS.json').read_text())['exports']
manifest=json.loads((E/'NFB_PEER_IMPORT.json').read_text())
r=ssh(a,'python3',f'''from pathlib import Path
import hashlib,json,shutil
source=Path('/home/dombarker/project-offloads/codex-cx-slice-q-mul4-cache-20261029')
cache=Path('/home/dombarker/project-offloads/codex-cx-slice-q-compose5-cache-20261029')
rows={rows!r};pins=[]
# Import EXACT peer exports into own flat cache. No peer write or deletion.
for r in rows:
 p=Path(r['destination']);assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256'];q=cache/(r['module'].replace('.','/')+'.olean');q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==r['sha256']
 else:shutil.copy2(p,q)
 pins.append(dict(source=str(p),destination=str(q),sha256=r['sha256'],source_sha256=r['source_sha256']))
# Peer source forests import NEV_ and emitted FIp helpers. Copy missing cache
# objects only, preserving relative module paths, and record every imported byte.
for p in source.rglob('*.olean'):
 rel=p.relative_to(source)
 if rel.parts[0].startswith('NFA_'):continue
 q=cache/rel
 if q.exists():continue
 q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
 pins.append(dict(source=str(p),destination=str(q),sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
print(json.dumps(pins))
''');assert r.returncode==0,r.stderr
(E/'NFB_PEER_OBJECT_PINS.json').write_text(r.stdout)
