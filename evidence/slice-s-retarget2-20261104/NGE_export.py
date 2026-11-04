"""Pin actual closure and retain owned proof/tool exports, no cache deletions."""
from pathlib import Path
import json,hashlib,lzma,os,subprocess
P=Path('/home/dombarker/project-offloads');B=P/'codex-cx-slice-s-retarget2-20261104';C=P/'codex-cx-slice-s-retarget2-cache-20261104';W=P/'codex-cx-sound-int2-20261025';T=Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0')
roots=[B/'NGE_objects',C/'NFY_exports_20261104',C/'NFY_priority',W,W/'objects',C,T/'lib/lean'];pins=[]
for row in map(json.loads,(B/'NGE_LOADED_scan.jsonl').read_text().splitlines()):
 rel=Path(row['module'].replace('.','/')+'.olean');p=next((r/rel for r in roots if (r/rel).is_file()),None);assert p,row['module']
 files=[]
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.is_file():files.append(dict(path=str(z),bytes=z.stat().st_size,sha256=hashlib.sha256(z.read_bytes()).hexdigest()))
 pins.append(dict(module=row['module'],selected_objects=files))
raw=json.dumps(dict(LEAN_PATH=[str(r) for r in roots],modules=pins),sort_keys=True).encode();(B/'NGE_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw,preset=6));(B/'NGE_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
exports=[]
for source,out in [(B/'NGE_objects',C/'NGE_exports_20261104'),(B/'NGE_generated',C/'NGE_exports_20261104'),(B/'NGE_native',C/'NGE_native_20261104')]:
 for src in source.rglob('*'):
  if not src.is_file():continue
  dst=out/src.relative_to(source);dst.parent.mkdir(parents=True,exist_ok=True)
  if not dst.exists():os.link(src,dst)
  else:assert dst.read_bytes()==src.read_bytes()
  exports.append(dict(path=str(dst),bytes=dst.stat().st_size,sha256=hashlib.sha256(dst.read_bytes()).hexdigest()))
(B/'NGE_EXPORT.json').write_text(json.dumps(dict(cache=str(C),workspace=str(B),exports=exports,closure_manifest_sha256=hashlib.sha256(raw).hexdigest(),disk=subprocess.check_output(['df','-h','/'],text=True),note='Owned exports hardlink owned scratch; all predecessor inputs were copied and hash-pinned; no cache removed'),indent=1)+'\n')
print(json.dumps(dict(modules=len(pins),exports=len(exports),bytes=sum(p['bytes'] for p in exports),closure_manifest_sha256=hashlib.sha256(raw).hexdigest())))
