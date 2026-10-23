#!/usr/bin/env python3
"""Collect the existing local compiled caller dependency overlay; no Lean runs.
Never write to any shared cache. Sources/objects are pinned for a focused
consumer check, not a coherent release rebuild of the imported closure.
"""
from pathlib import Path
import json,re,subprocess,hashlib,sys
R=Path(__file__).resolve().parents[5];B=R/'docs/research/100bit-spend-path-20261013'
cfg=json.loads((B/'evidence/s126-current-caller-20261021/s2-sdk-ready-raw-inputs-v1/command.json').read_text());paths=[Path(p) for p in cfg['lean_path'].split(':')]
source_paths=[Path(p) for p in subprocess.check_output(['rg','--files','-g','*.lean'],cwd=R,text=True).splitlines()]
byname={}
for p in source_paths:byname.setdefault(p.stem,[]).append(R/p)
roots=[B/'lean-candidates/s126-caller-boundary-20261021',B/'lean',R/'AspisFormal']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
seen={};skip=[]
def collect(m):
 if m in seen or m in skip:return
 if m.split('.')[0] in ['Init','Std','Lean','Mathlib','Aeneas','AeneasMeta','Batteries','Aesop','Qq','ProofWidgets','Lake']:skip.append(m);return
 rel=Path(m.replace('.','/'))
 obj=next((p/rel.with_suffix('.olean') for p in paths if (p/rel.with_suffix('.olean')).is_file()),None)
 preferred=[p/rel.with_suffix('.lean') for p in roots]
 sources=[p for p in preferred if p.is_file()]
 if not sources:sources=[p for p in byname.get(rel.name,[]) if str(p).endswith('/'+m.replace('.','/')+'.lean')]
 if not sources:
  seen[m]={'source':None,'source_candidates':{},'object':str(obj) if obj else None,'object_sha256':sha(obj) if obj else None,'imports':[],'source_selection':'unresolved source; no attribution'}
  return
 src=sources[0]
 imports=sorted({v for src in sources for line in src.read_text().splitlines() if line.startswith('import ') for v in re.sub(r'--.*','',line[7:]).split()})
 seen[m]={'source':str(src) if len(sources)==1 else None,'source_sha256':sha(src) if len(sources)==1 else None,'source_candidates':{str(src):sha(src) for src in sources},'source_selection':'unique' if len(sources)==1 else 'ambiguous: object pin only, union of candidate imports is overinclusive; no source attribution','object':str(obj) if obj else None,'object_sha256':sha(obj) if obj else None,'imports':imports}
 for i in imports:collect(i)
collect('S2SdkReadyRawInputsV1')
out=Path(sys.argv[1]);out.mkdir(exist_ok=True)
for m,r in seen.items():
 if r['object']:
  dest=out/(m.replace('.','/')+'.olean');dest.parent.mkdir(parents=True,exist_ok=True)
  # Symlink ONLY in our fresh staging tree, never the source cache.
  dest.symlink_to(r['object'])
manifest={'modules':seen,'external_cached_modules':skip,'qualification':__doc__}
(B/'evidence/s2a-20261023/S2A-import-overlay.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'modules':len(seen),'missing_objects':[m for m,r in seen.items() if r['object'] is None]}))
