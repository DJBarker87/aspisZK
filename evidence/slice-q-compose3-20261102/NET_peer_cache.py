from pathlib import Path
import json,hashlib,sys
from NET_remote import ssh
E=Path(__file__).resolve().parent
P=Path('/private/tmp/NET_peer_5d12713_20261103/evidence/slice-q-mul2-20261101')
manifest=json.loads((P/'NEI_CACHE_EXPORTS.json').read_text())
code=f'''from pathlib import Path
import json,hashlib
m={manifest!r}
roots=[Path('/home/dombarker/project-offloads/codex-cx-slice-q-compose3-cache-20261029'),Path('/home/dombarker/project-offloads/codex-cx-slice-q-compose3-cache-20261029/NEB_exports_20261029'),Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'),Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects')]
out=[]
for o in m['objects']:
 p=Path(o['path']);data=p.read_bytes();assert hashlib.sha256(data).hexdigest()==o['sha256']
 rel=p.relative_to(m['cache'])
 existing=[dict(path=str(r/rel),sha256=hashlib.sha256((r/rel).read_bytes()).hexdigest()) for r in roots if (r/rel).is_file()]
 out.append(dict(**o,relative=str(rel),existing=existing))
print(json.dumps(out))
'''
r=ssh('NET_PEER_CACHE_CHECK','python3',code);assert r.returncode==0,r.stderr
(E/'NET_PEER_CACHE_CHECK.json').write_text(r.stdout)
x=json.loads(r.stdout);print('objects',len(x),'collisions',sum(bool(o['existing']) for o in x),'different',[(o['relative'],z['path']) for o in x for z in o['existing'] if z['sha256']!=o['sha256']])
