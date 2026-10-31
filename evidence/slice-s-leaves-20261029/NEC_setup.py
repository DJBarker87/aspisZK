from pathlib import Path
import hashlib,json,shutil
P=Path('/home/dombarker/project-offloads'); B=P/'codex-cx-slice-s-leaves-20261029'; C=P/'codex-cx-slice-s-leaves-cache-20261029'; S=P/'codex-cx-sound-int2-20261025'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
imports=[]
for name in ['codex-cx-leaf-cache-20261027','codex-cx-cpilot-cache-20261028','codex-cx-front2-cache-20261028','codex-cx-front4-cache-20261028']:
 for p in (P/name).rglob('*.olean'):
  rel=p.relative_to(P/name); q=C/rel
  h=sha(p)
  if q.exists():
   imports.append(dict(source=str(p),destination=str(q),sha256=h,selected=sha(q)==h));continue
  q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
  imports.append(dict(source=str(p),destination=str(q),sha256=h,selected=True))
for name in ['S2W_run_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:
 p=S/name
 if p.exists():shutil.copy2(p,B/name)
for n in ['NEC_objects','NEC_generated','NEC_tmp']: (B/n).mkdir(exist_ok=True)
pins={str(p):dict(path=str(p),sha256=sha(p)) for p in C.rglob('*.olean')}
# Pin every coherent object, including the actual Aeneas library objects resolved below.
for root in [S,S/'objects']:
 for p in root.rglob('*.olean'):
  if root==S and ('objects' in p.relative_to(S).parts or len(p.relative_to(S).parts)>1):continue
  pins[str(p)]=dict(path=str(p),sha256=sha(p))
(B/'NEC_CACHE_IMPORTS.json').write_text(json.dumps(imports,indent=1)+'\n')
(B/'NEC_OBJECT_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
print(json.dumps(dict(imported=len(imports),pinned=len(pins),cache=str(C))))
