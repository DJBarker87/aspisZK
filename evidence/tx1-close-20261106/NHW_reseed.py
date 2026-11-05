"""Copy only retained proof objects; preserve all existing first resolutions."""
from pathlib import Path
import json,hashlib,shutil
B=Path(__file__).resolve().parent;C=Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NHW_seed_20261106')
roots=json.loads((B/'NHW_PATHS.json').read_text());pins=[]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def cp(p,d):
 q=d/p.name;d.mkdir(exist_ok=True)
 if q.exists():assert sha(q)==sha(p)
 else:shutil.copy2(p,q)
 pins.append(dict(source=str(p),path=str(q),sha256=sha(q),bytes=q.stat().st_size))
seen=set();ngk=C/'NGK_selected'
for root in roots:
 for p in sorted(Path(root).glob('NGK_*.olean')):
  if p.name in seen:continue
  seen.add(p.name)
  for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
   if z.exists():cp(z,ngk)
ngrs=C/'NGR_NGS_selected'
for row in json.loads((B/'NHW_NGR_NGS_EXPORTS.json').read_text()):
 p=Path(row['path']);assert sha(p)==row['sha256']
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.exists():cp(z,ngrs)
paths=list(dict.fromkeys([roots[0],str(ngk),str(ngrs)]+roots[1:]))
(B/'NHW_PATHS.json').write_text(json.dumps(paths,indent=1)+'\n')
(B/'NHW_ADDITIONAL_SEED.json').write_text(json.dumps(dict(files=pins,bytes=sum(p['bytes'] for p in pins)),indent=1)+'\n')
print(json.dumps(dict(files=len(pins),bytes=sum(p['bytes'] for p in pins))))
