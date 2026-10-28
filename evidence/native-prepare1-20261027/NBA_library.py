"""Read-only complete Aeneas object/sidecar pin. Initial main-object pin retained."""
from pathlib import Path
import subprocess,json,hashlib,datetime
E=Path(__file__).resolve().parent
roots=['/home/dombarker/project-offloads/codex-cx-leaf-cache-20261027','/home/dombarker/project-offloads/codex-cx-assoc-a2-cache-20261027/XRw_objects','/home/dombarker/project-offloads/codex-cx-sound-int2-20261025','/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects','/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean']
code='''from pathlib import Path
import hashlib,json,datetime
roots=[Path(p) for p in ROOTS]
names=set()
for r in roots:
 for p in list(r.glob('Aeneas.*'))+list((r/'Aeneas').rglob('*')):
  if p.is_file() and ('.olean' in p.name or p.suffix=='.ir'):names.add(str(p.relative_to(r)))
selected={n:next(r/n for r in roots if (r/n).is_file()) for n in names}
print(json.dumps(dict(time=datetime.datetime.now(datetime.timezone.utc).isoformat(),objects={n:dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for n,p in selected.items()})))
'''.replace('ROOTS',repr(roots))
r=subprocess.run(['ssh','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True);assert r.returncode==0,r.stderr
x=json.loads(r.stdout);m=json.loads(Path('evidence/sound-int2-20261025/object-source-manifest.json').read_text())['modules'];expected={}
for n,v in m.items():
 if n=='Aeneas' or n.startswith('Aeneas.'):
  key=n.replace('.','/')+'.olean';expected[key]=v['sha256']
  for side,h in v.get('sidecars',{}).items():expected[str(Path(key).parent/side)]=h['sha256'] if isinstance(h,dict) else h
assert all(x['objects'][k]['sha256']==h for k,h in expected.items())
start=json.loads((E/'NBA_LIBRARY_START.json').read_text());assert all(next(v for v in x['objects'].values() if v['path']==p)['sha256']==h['sha256'] for p,h in start.items())
x.update(inherited_expected=expected,all_inherited_matches=True,initial_main_objects=len(start),qualification='219 main objects freshly pinned at original start. Sidecars freshly captured now and independently matched inherited SInt2 hashes; not claimed as fresh original-start captures.')
p=E/'NBA_LIBRARY_COMPLETE.json'
if p.exists():
 old=json.loads(p.read_text());assert old['objects']==x['objects'];p=E/'NBA_LIBRARY_COMPLETE_END.json'
p.write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(dict(objects=len(x['objects']),inherited_expected=len(expected),all_match=True)))
