"""Read-only closure pins and retained owned exports; never delete the cache."""
from pathlib import Path
import shutil,hashlib,json,lzma,subprocess
P=Path('/home/dombarker/project-offloads');B=P/'codex-cx-slice-s-retarget3-20261104';C=P/'codex-cx-slice-s-retarget3-cache-20261104';W=P/'codex-cx-sound-int2-20261025';T=Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0')
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();pins=[]
for directory in ['NGF_objects','NGF_generated','NGF_native']:
 for p in (B/directory).rglob('*'):
  if not p.is_file():continue
  dest=C/('NGF_exports_20261104' if directory!='NGF_native' else 'NGF_native_20261104')/p.relative_to(B/directory);dest.parent.mkdir(parents=True,exist_ok=True)
  if dest.exists():assert H(p)==H(dest)
  else:shutil.copy2(p,dest)
  assert H(p)==H(dest);pins.append(dict(path=str(dest),sha256=H(dest),bytes=dest.stat().st_size))
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:assert H(B/'NGF_native'/n)==H(C/'NFY_native_20261104'/n)
roots=[B/'NGF_objects',C/'NFY_exports_20261104',C/'NFY_priority',W,W/'objects',C,T/'lib/lean'];scan=[json.loads(l) for l in (B/'NGF_LOADED_scan.jsonl').read_text().splitlines()];closure=[]
for r in scan:
 rel=r['module'].replace('.','/')+'.olean';p=next((root/rel for root in roots if (root/rel).is_file()),None);assert p,r['module']
 for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if q.is_file():closure.append(dict(module=r['module'],path=str(q),sha256=H(q),bytes=q.stat().st_size))
raw=json.dumps(dict(LEAN_PATH=[str(r) for r in roots],selected_objects=closure),sort_keys=True).encode();(B/'NGF_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw,preset=6));(B/'NGF_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
size=subprocess.check_output(['du','-sb',str(C)],text=True);disk=subprocess.check_output(['df','-h',str(C)],text=True)
out=dict(cache_retained=str(C),workspace_retained=str(B),exports=pins,closure_manifest_sha256=hashlib.sha256(raw).hexdigest(),closure_modules=len(scan),du_bytes=size,disk=disk,note='All own and predecessor cache objects retained; no cache deletion, source change or recompile. All sources and sidecar hashes pinned. Native binaries are artifacts, only hashes committed.')
(B/'NGF_EXPORT.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(dict(exports=len(pins),closure=len(closure),size=size)))
