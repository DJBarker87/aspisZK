"""Complete the pinned library manifest with coupled .olean private/server artifacts."""
from pathlib import Path
import hashlib,json,shutil
P=Path('/home/dombarker/project-offloads');B=P/'codex-cx-slice-s-leaves-20261029';S=P/'codex-cx-sound-int2-20261025'
C=P/'codex-cx-slice-s-leaves-cache-20261029'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
old=json.loads((B/'NEC_OBJECT_PINS.json').read_text());imports=json.loads((B/'NEC_CACHE_IMPORTS.json').read_text());owners={}
for entry in imports:
 if entry['selected']:owners.setdefault(entry['destination'],entry['source'])
copied=[]
for dest,source in owners.items():
 d=Path(dest);p=Path(source)
 assert sha(d)==sha(p)
 for q in p.parent.glob(p.name+'.*'):
  if not q.is_file() or not q.name.endswith(('.olean.private','.olean.server')):continue
  out=d.parent/q.name
  if out.exists():assert sha(out)==sha(q)
  else:shutil.copy2(q,out)
  copied.append(dict(source=str(q),destination=str(out),sha256=sha(q),public_sha256=sha(p)))
pins={};coupling=[]
for root,recursive in [(S,False),(S/'objects',True),(C,True),(B/'NEC_objects',True)]:
 for p in (root.rglob('*.olean.*') if recursive else root.glob('*.olean.*')):
  if not p.is_file() or not p.name.endswith(('.olean.private','.olean.server')):continue
  public=p.with_name(p.name.split('.olean',1)[0]+'.olean');assert public.exists(),str(public)
  if str(public) in old:assert sha(public)==old[str(public)]['sha256']
  pins[str(p)]=dict(path=str(p),sha256=sha(p))
  coupling.append(dict(sidecar=str(p),public=str(public),public_sha256=sha(public),sidecar_sha256=sha(p)))
(B/'NEC_SIDECAR_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
(B/'NEC_SIDECAR_COUPLING.json').write_text(json.dumps(dict(copied=copied,coupling=coupling,policy='Select sidecars only from the same read-only source owner as the copied public object; never mix owners or overwrite mismatched artifacts.'),indent=1)+'\n')
print(json.dumps(dict(sidecars=len(pins),copied=len(copied),aeneas_sidecars=[n for n in pins if '/Aeneas/' in n])))
