"""Pin the selected scanned closure and compare it to committed NGR evidence."""
from pathlib import Path
import json,hashlib,lzma,shutil
B=Path('/home/dombarker/project-offloads/codex-cx-carriers-bind-20261105')
C=Path('/home/dombarker/project-offloads/codex-cx-carriers-bind-cache-20261104')
config=json.loads((B/'NGS_L016.json').read_text());roots=[Path(x) for x in config['env']['LEAN_PATH'].split(':')]
scan=[json.loads(x) for x in (B/'NGS_LOADED_scan.jsonl').read_text().splitlines()]
selected=[]
for row in scan:
 module=row['module'];rel=module.replace('.','/')+'.olean';obj=next((r/rel for r in roots if (r/rel).is_file()),None);assert obj,module
 for p in [obj,Path(str(obj)+'.private'),Path(str(obj)+'.server'),obj.with_suffix('.ir')]:
  if p.is_file():selected.append(dict(module=module,path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
def key(r):return r['module'],next(s for s in ['.olean.private','.olean.server','.olean','.ir'] if r['path'].endswith(s))
actual={key(r):r for r in selected}
priorPath=Path('/home/dombarker/project-offloads/codex-cx-history-persist-20261105/NGR_CLOSURE_PINS.json.xz')
prior=json.loads(lzma.decompress(priorPath.read_bytes()))['selected_objects']
missing=[];mismatches=[];same=0
for r in prior:
 n=actual.get(key(r))
 if not n:missing.append(key(r))
 elif r['sha256']!=n['sha256']:mismatches.append(dict(module=r['module'],old=r,new=n))
 else:same+=1
not_in_target=[x for x in missing if x==('NGR_COMBINED_IMPORT','.olean')]
missing=[x for x in missing if x not in not_in_target]
assert not missing and not mismatches,(missing,mismatches)
summary=dict(shared_NGR_objects=same,missing=missing,not_in_target_closure=not_in_target,mismatches=mismatches,prior_path=str(priorPath),prior_sha256=hashlib.sha256(priorPath.read_bytes()).hexdigest())
raw=json.dumps(dict(LEAN_PATH=[str(r) for r in roots],selected_objects=selected,NGR_comparison=summary)).encode()
(B/'NGS_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw,preset=6));(B/'NGS_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
(B/'NGS_PIN_COMPARISON.json').write_text(json.dumps(dict(files=len(selected),bytes=sum(r['bytes'] for r in selected),sha256=hashlib.sha256(raw).hexdigest(),comparison=summary),indent=1)+'\n')
exports=[];out=C/'NGS_exports_20261105';out.mkdir(exist_ok=True)
for module in ['NGS_Selection','NGS_CheckpointRead','NGS_Carriers','NGS_IssuedCarriers','NGS_PersistedCarriers','NGS_COMBINED_IMPORT']:
 for suffix in ['.olean','.olean.private','.olean.server','.ir']:
  src=B/'NGS_objects'/(module+suffix)
  if src.is_file():
   dst=out/src.name;shutil.copy2(src,dst);sha=hashlib.sha256(src.read_bytes()).hexdigest();assert hashlib.sha256(dst.read_bytes()).hexdigest()==sha
   exports.append(dict(module=module,path=str(dst),sha256=sha,bytes=dst.stat().st_size,source_sha256=hashlib.sha256((B/'NGS_generated'/(module+'.lean')).read_bytes()).hexdigest()))
(B/'NGS_EXPORT.json').write_text(json.dumps(exports,indent=1)+'\n')
print(json.dumps(dict(files=len(selected),NGR_shared=same,export_files=len(exports),export_bytes=sum(r['bytes'] for r in exports))))
