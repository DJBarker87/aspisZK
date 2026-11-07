"""Retain validated objects and inspect only the owned host workspace."""
from pathlib import Path
import json,hashlib,shutil,os
B=Path.cwd();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
exec((B/'NLW_export.py').read_text())
rows=json.loads((B/'NLW_ATTEMPTS_INDEX.json').read_text());snapshots=0;library={}
for row in rows:
 a=row['attempt'];r=json.loads((B/a/'receipt.json').read_text())
 for n,h in r.get('source_hashes',{}).items():
  p=B/a/'sources'/n
  if p.is_file():assert sha(p)==h,(a,n);snapshots+=1
 cfg=json.loads((B/(a+'.json')).read_text())
 for n,pin in cfg.get('deps_fingerprint',{}).get('selected_objects',{}).items():
  if '/Aeneas/' in n or '/AeneasMeta/' in n or Path(n).name in ['Aeneas.olean','AeneasMeta.olean']:
   if n in library:assert library[n]==pin['sha256'],n
   library[n]=pin['sha256']
for n,h in library.items():assert sha(Path(n))==h,n
size=sum(p.stat().st_size for p in B.rglob('*') if p.is_file())
assert size<30_000_000_000,size
free=shutil.disk_usage(B).free
ret=dict(workspace=str(B),bytes=size,free_bytes=free,limit_bytes=30_000_000_000,
 cargo_target_dir=str(B/'NLW_target'),tmpdir=str(B/'NLW_tmp'),deletions=0,source_snapshots_checked=snapshots,
 stable_aeneas_objects=len(library),retained_cache=True,scopes=[r['attempt'] for r in rows])
(B/'NLW_RETENTION.json').write_text(json.dumps(ret,indent=1)+'\n')
(B/'NLW_TOOL_PINS.json').write_text(json.dumps(dict(lean_sysroot=os.environ['LEAN_SYSROOT'],
 lean_path=os.environ['LEAN_PATH'].split(':'),library_objects=library,
 cargo_target_dir=os.environ['CARGO_TARGET_DIR'],tmpdir=os.environ['TMPDIR'],
 frozen_release='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',pool_source='b936275465',
 lock_and_feature_graph='per-Kani NLW_K*-graph.json and post-lock receipts; offline; no cargo-kani --locked',
 kmx_patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67',
 extraction_invocations=0,elf_rebuilds=0,elf_pins_inherited=True),indent=1)+'\n')
print(json.dumps(dict(workspace_bytes=size,free_bytes=free,source_snapshots_checked=snapshots,aeneas_objects=len(library))))
