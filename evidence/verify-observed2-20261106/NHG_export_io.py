"""Cache packaging only: no Lean, Rust, Kani, extraction or arithmetic gate."""
from pathlib import Path
import json,hashlib,shutil,lzma,time
B=Path('/home/dombarker/project-offloads/codex-cx-verify-observed2-20261106')
C=Path('/home/dombarker/project-offloads/codex-cx-prepared-claim-cache-20261104/NHG_exports_20261106')
start=time.monotonic();C.mkdir(parents=True,exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
roots=json.loads((B/'NHG_FINAL_EXPORT_INPUT.json').read_text())['lean_path'];modules=json.loads((B/'NHG_FINAL_EXPORT_INPUT.json').read_text())['modules'];copied={}
for module in modules:
 p=B/'NHG_objects'/(module+'.olean');assert p.is_file(),module
 for src in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if src.is_file():
   dest=C/src.name;h=sha(src)
   if dest.exists():assert sha(dest)==h
   else:shutil.copy2(src,dest)
   copied[src.name]=dict(path=str(dest),bytes=dest.stat().st_size,sha256=h)
(C/'bin').mkdir(exist_ok=True)
for name in ['NHG_ProofDriver','NHG_Driver']:
 src=B/'NHG_native'/name;dest=C/'bin'/name;h=sha(src)
 if dest.exists():assert sha(dest)==h
 else:shutil.copy2(src,dest)
 copied['bin/'+name]=dict(path=str(dest),bytes=dest.stat().st_size,sha256=h)
closure={};loaded=[json.loads(l)['module']for l in(B/'NHG_LOADED_scan.jsonl').read_text().splitlines()]
for module in loaded:
 rel=module.replace('.','/')+'.olean';src=next((Path(root)/rel for root in roots if (Path(root)/rel).is_file()),None);assert src is not None,module
 for path in [src,Path(str(src)+'.private'),Path(str(src)+'.server'),src.with_suffix('.ir')]:
  if path.is_file():closure[str(path)]=dict(bytes=path.stat().st_size,sha256=sha(path))
raw=json.dumps(closure,sort_keys=True).encode();(B/'NHG_FINAL_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw,preset=6));(B/'NHG_FINAL_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
report=dict(kind='packaging_io',formal_tool_invocations=0,export_path=str(C),exported_files=copied,exported_bytes=sum(x['bytes']for x in copied.values()),closure_objects=len(closure),loaded_modules=len(loaded),closure_sha256=hashlib.sha256(raw).hexdigest(),lean_path=[str(C)]+roots[1:],wall_seconds=time.monotonic()-start,cache_deleted=False)
(B/'NHG_EXPORT.json').write_text(json.dumps(report,indent=1)+'\n');(C/'NHG_EXPORT.json').write_text(json.dumps(report,indent=1)+'\n');print(json.dumps({k:report[k]for k in ['kind','formal_tool_invocations','export_path','exported_bytes','closure_objects','loaded_modules','wall_seconds']}))
