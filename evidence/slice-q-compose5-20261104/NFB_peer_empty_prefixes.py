from NFB_remote import *
assert not (E/'NFB_ACTIVE.json').exists()
a='NFB_PEER_EMPTY_PREFIXES';admit(a)
r=ssh(a,'python3',f'''from pathlib import Path
import json
c=Path('/home/dombarker/project-offloads/codex-cx-slice-q-compose5-cache-20261029');keep=c/'NFB_retained_empty_prefixes';keep.mkdir(exist_ok=True);moved=[]
for p in list(c.iterdir()):
 if not p.is_dir() or p.name.startswith('NFB_'):continue
 if any(x.is_file() for x in p.rglob('*')):continue
 q=keep/p.name;assert not q.exists();p.rename(q);moved.append(dict(old=str(p),new=str(q)))
print(json.dumps(dict(reason='Empty module-prefix directories shadow fallback search even after objects are relocated. Retain the empty directory trees outside the resolved prefix root.',moved=moved)))
''');assert r.returncode==0,r.stderr
(E/'NFB_PEER_EMPTY_PREFIXES.json').write_text(r.stdout)
