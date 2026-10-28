"""Read-only audit of actual LEAN_PATH library selection; no compiler is run."""
from pathlib import Path
import sys,importlib.util,json
E=Path(__file__).resolve().parent;sys.argv=['pins','none']
s=importlib.util.spec_from_file_location('NBK_native',E/'NBK_native.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
r=m.py('''from pathlib import Path
import hashlib,json
b=Path('/home/dombarker/project-offloads/codex-cx-native-tx2e-20261027')
roots=[Path('/home/dombarker/project-offloads/codex-cx-leaf-cache-20261027'),Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'),Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects'),Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')]
expected=json.loads((b/'NBK_LIBRARY_PIN.json').read_text());selected={}
for old,pin in expected.items():
 rel=Path(old).relative_to(roots[2]);candidates=[root/rel for root in roots];p=next(x for x in candidates if x.is_file())
 got={'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}
 assert got['sha256']==pin['sha256'] and got['bytes']==pin['bytes'],(old,got)
 selected[str(rel)]=got
print(json.dumps({'lean_path':[str(p) for p in roots],'selected':selected,'all_resolved_objects_match_pinned_library':True},indent=2))
''')
assert r.returncode==0,r.stdout+r.stderr
(E/'NBK_RESOLVED_LIBRARY_PIN.json').write_text(r.stdout)
print('actual LEAN_PATH Aeneas resolution matches all pinned objects')
