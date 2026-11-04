"""Read-only pinning of the actually scanned module selection on the build host."""
from pathlib import Path
import json,hashlib,lzma
B=Path('/home/dombarker/project-offloads/codex-cx-history-persist-20261105')
cfg=json.loads((B/'NGR_L019.json').read_text());roots=[Path(x) for x in cfg['env']['LEAN_PATH'].split(':')]
scan=[json.loads(x) for x in (B/'NGR_LOADED_scan.jsonl').read_text().splitlines()]
selected=[]
for row in scan:
 module=row['module'];rel=module.replace('.','/')+'.olean'
 obj=next((r/rel for r in roots if (r/rel).is_file()),None)
 assert obj is not None,module
 for p in [obj,Path(str(obj)+'.private'),Path(str(obj)+'.server'),obj.with_suffix('.ir')]:
  if p.is_file():
   selected.append(dict(module=module,path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
def key(r):
 return r['module'],next(s for s in ['.olean.private','.olean.server','.olean','.ir'] if r['path'].endswith(s))
actual={key(r):r for r in selected}
comparisons={}
prior=json.loads(lzma.decompress((B/'NGR_PRIOR_PINS.json.xz').read_bytes()))
for label,rows in prior.items():
 missing=[];mismatches=[];same=0
 for r in rows:
  k=key(r);new=actual.get(k)
  # NGP's statement-only modules not in this closure are not lost dependencies.
  if not new:
   missing.append(dict(module=k[0],kind=k[1]));continue
  if r['sha256']!=new['sha256']:
   mismatches.append(dict(module=k[0],kind=k[1],old=r['sha256'],new=new['sha256'],old_path=r['path'],new_path=new['path']))
  else:same+=1
 comparisons[label]=dict(same=same,not_in_target_closure=missing,mismatches=mismatches)
raw=json.dumps(dict(LEAN_PATH=[str(r) for r in roots],selected_objects=selected,comparisons=comparisons)).encode()
(B/'NGR_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw,preset=6));(B/'NGR_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
summary=dict(files=len(selected),bytes=sum(r['bytes'] for r in selected),sha256=hashlib.sha256(raw).hexdigest(),comparisons=comparisons)
(B/'NGR_PIN_COMPARISON.json').write_text(json.dumps(summary,indent=1)+'\n');print(json.dumps(summary))
