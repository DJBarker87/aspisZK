"""Read-only seal of the selected final closure and retained predecessor objects."""
from pathlib import Path
import json,lzma,hashlib
B=Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NNN_20261111');M=B.parent/'NNM_20261111'
paths=json.loads((B/'NNN_PATHS.json').read_text());rows=list(map(json.loads,(B/'NNN_LOADED_scan.jsonl').read_text().splitlines()));selected=[];companions=[]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
T=Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
for x in rows:
 rel=x['module'].replace('.','/')+'.olean';p=next((Path(r)/rel for r in paths+[str(T)]if(Path(r)/rel).is_file()),None);assert p,rel
 selected.append(dict(module=x['module'],path=str(p),sha256=sha(p),bytes=p.stat().st_size))
 for q in [Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if q.is_file():companions.append(dict(module=x['module'],path=str(q),sha256=sha(q),bytes=q.stat().st_size))
old=json.loads(lzma.open(M/'NNM_CLOSURE_PINS.json.xz').read());by={x['module']:x for x in selected};unchanged=[]
for x in old['selected_objects']:
 if not x['path'].endswith('.olean'):continue
 assert by[x['module']]['sha256']==x['sha256'],x['module'];unchanged.append(x['module'])
# The ledger29 pin manifest stores olean and sidecars together. Compare all of them.
available={(z['module'],Path(z['path']).name[len(z['module'].split('.')[-1]):]):z for z in selected+companions}
sidechecks=0
for z in old['selected_objects']:
 suffix=Path(z['path']).name[len(z['module'].split('.')[-1]):]
 assert available[(z['module'],suffix)]['sha256']==z['sha256'],(z['module'],suffix)
 sidechecks+=not z['path'].endswith('.olean')
out=dict(selected_objects=selected,companion_objects=companions,predecessor_modules_unchanged=len(unchanged),predecessor_companions_unchanged=sidechecks,predecessor_module_names=unchanged,status='PASS',LEAN_PATH=paths)
raw=(json.dumps(out,sort_keys=True,indent=1)+'\n').encode();(B/'NNN_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw));(B/'NNN_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
# Preserve all own selected outputs; prior exports remain read-only and retained.
export=B/'NNN_exports';records=[dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size)for p in sorted(export.iterdir())if p.is_file()]
(B/'NNN_EXPORT.json').write_text(json.dumps(dict(export=str(export),LEAN_PATH=paths,files=records,closure_sha256=hashlib.sha256(raw).hexdigest(),scope='Coherent cached closure, not a cold frozen release rebuild'),indent=1)+'\n')
print(json.dumps(dict(status='PASS',modules=len(rows),predecessor_modules_unchanged=len(unchanged),companions=len(companions))))
