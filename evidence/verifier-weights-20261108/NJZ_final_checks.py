"""Owned read-only closure validation and retained export; no shared cache writes."""
from pathlib import Path
import json,hashlib,lzma,shutil,subprocess
B=Path(__file__).resolve().parent;C=B.parent/'codex-cx-slice-d-prepared-cache-20261104';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
paths=[Path(p) for p in json.loads((B/'NJZ_PATHS.json').read_text())]
scan=[json.loads(l) for l in (B/'NJZ_LOADED_scan.jsonl').read_text().splitlines()]
assert scan and all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in scan)
closure=[]
for row in scan:
 rel=row['module'].replace('.','/')+'.olean';p=next((root/rel for root in paths if (root/rel).is_file()),None);assert p is not None,rel
 for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if q.is_file():closure.append(dict(module=row['module'],path=str(q),sha256=sha(q),bytes=q.stat().st_size))
raw=(json.dumps(closure,sort_keys=True,indent=1)+'\n').encode();(B/'NJZ_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw,preset=6));(B/'NJZ_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
modules=json.loads((B/'NJZ_MODULES.json').read_text())+['NJZ_COMBINED_IMPORT','NJZ_ProofDriver','NJZ_Driver'];export=C/'NJZ_exports_20261108';export.mkdir(exist_ok=True);exports=[]
for name in modules:
 p=B/'NJZ_objects'/(name+'.olean');assert p.is_file(),name
 for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if not q.is_file():continue
  dest=export/q.name
  if dest.exists():assert sha(dest)==sha(q),('retained cache cannot be overwritten',dest)
  else:shutil.copyfile(q,dest)
  assert sha(dest)==sha(q)
  exports.append(dict(module=name,source=str(q),retained=str(dest),sha256=sha(q),bytes=q.stat().st_size))
(B/'NJZ_EXPORT.json').write_text(json.dumps(dict(directory=str(export),bytes=sum(x['bytes'] for x in exports),files=exports),indent=2)+'\n')
errors=[];sources=[]
for name in modules:
 p=B/'NJZ_generated'/(name+'.lean');assert p.is_file()
 sources.append(dict(module=name,path=str(p),sha256=sha(p),bytes=p.stat().st_size))
for n,h in json.loads((B/'NJZ_SOURCE_PINS.json').read_text()).items():
 if sha(B/'NJZ_src'/n)!=h:errors.append(n)
assert not errors,errors
(B/'NJZ_SOURCE_VERIFICATION.json').write_text(json.dumps(dict(status='PASS',unchanged_frozen_files=len(json.loads((B/'NJZ_SOURCE_PINS.json').read_text())),errors=errors,sources=sources,closure_files=len(closure),closure_bytes=sum(r['bytes'] for r in closure),CARGO_TARGET_DIR=str(B/'NJZ_target')),indent=2)+'\n')
tools=[]
for p in [Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin')/n for n in ['lean','lake','leanc']]+[Path('/home/dombarker/.cargo/bin/cargo-kani')]+[B/'S2W_run_host.py',B/'S2W_lean_host.py']:
 assert p.is_file();tools.append(dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size))
(B/'NJZ_TOOL_PINS.json').write_text(json.dumps(dict(tools=tools,lean_toolchain=(B/'lean-toolchain').read_text().strip(),Aeneas=[r for r in closure if '/Aeneas' in r['path']]),indent=2)+'\n')
(B/'NJZ_RETENTION.json').write_text(json.dumps(dict(cache_preserved=True,seed=str(C/'NJZ_seed_20261108'),retained_export=str(export),free_bytes=shutil.disk_usage(B).free,removed=[],keys_or_wallets_touched=False),indent=2)+'\n')
print(json.dumps(dict(status='PASS',closure_files=len(closure),export_files=len(exports),export_bytes=sum(x['bytes'] for x in exports),free_bytes=shutil.disk_usage(B).free)))
