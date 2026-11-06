from pathlib import Path
import json,hashlib,lzma,shutil,os
B=Path(__file__).resolve().parent;C=B.parent/'codex-cx-slice-d-prepared-cache-20261104';roots=os.environ['LEAN_PATH'].split(':')
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for block in iter(lambda:f.read(1048576),b''):h.update(block)
 return h.hexdigest()
selected=json.loads((B/'NJC_MODULES.json').read_text())['selected'];checks=[]
for row in selected:
 p=B/'NJC_generated'/(row['module']+'.lean');assert sha(p)==row['source_sha256'];checks.append(dict(module=row['module'],sha256=sha(p)))
pins=json.loads((B/'NJC_SOURCE_PINS.json').read_text());errors=[n for n,h in pins.items() if sha(B/'NJC_src'/n)!=h];assert not errors,errors
assert sha(B/'NJC_src/Cargo.lock')=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
seed=json.loads((B/'NJC_SEED.json').read_text());seed=seed.get('seed',seed) if isinstance(seed,dict) else seed
for row in seed:assert sha(Path(row['source']))==sha(Path(row['destination']))==row['sha256']
# Predecessor export was copied first. Add only the small retained NIU composition export.
niuroot=B.parent/'codex-cx-ledger8-cache-20261104/NIU_20261107/NIU_exports_20261107';niuseed=C/'NJC_NIU_seed_20261107';niuseed.mkdir(exist_ok=True);imported=[]
for p in sorted(niuroot.iterdir()):
 if not p.is_file():continue
 q=niuseed/p.name
 if q.exists():assert sha(p)==sha(q)
 else:shutil.copyfile(p,q)
 imported.append(dict(source=str(p),destination=str(q),sha256=sha(q),bytes=q.stat().st_size))
closure=[];modules=[json.loads(l)['module'] for l in (B/'NJC_LOADED_scan.jsonl').read_text().splitlines()]
for module in modules:
 rel=module.replace('.','/')+'.olean';p=next((Path(r)/rel for r in roots if (Path(r)/rel).is_file()),None);assert p is not None,module
 for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if q.is_file():closure.append(dict(module=module,path=str(q),sha256=sha(q),bytes=q.stat().st_size))
raw=json.dumps(closure,separators=(',',':')).encode();(B/'NJC_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw,preset=6));(B/'NJC_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
export=C/'NJC_exports_20261107';export.mkdir(exist_ok=True);exports=[]
for module in [r['module'] for r in selected]+['NJC_COMBINED_IMPORT']:
 p=B/'NJC_objects'/(module+'.olean')
 for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if not q.exists():continue
  out=export/q.name;shutil.copyfile(q,out);assert sha(q)==sha(out)
  exports.append(dict(source=str(q),path=str(out),sha256=sha(out),bytes=out.stat().st_size))
(B/'NJC_SOURCE_VERIFICATION.json').write_text(json.dumps(dict(status='PASS',selected_sources=checks,staged_sources=len(pins),errors=errors,seed_verified=len(seed),NIU_imported=imported),indent=1)+'\n')
(B/'NJC_TOOL_PINS.json').write_text(json.dumps(dict(launcher={n:sha(B/n) for n in ['S2W_run_host.py','S2W_lean_host.py']},walker_C=sha(B/'NJC_native/NFA_WALKER.c'),memory_C=sha(B/'NJC_native/NFA_MemoryLimit.c')),indent=1)+'\n')
(B/'NJC_EXPORT.json').write_text(json.dumps(dict(path=str(export),files=exports,bytes=sum(r['bytes'] for r in exports),closure_files=len(closure)),indent=1)+'\n')
(B/'NJC_RETENTION.json').write_text(json.dumps(dict(retained=[str(export),str(C/'NJC_seed_20261107'),str(niuseed)],free_bytes=shutil.disk_usage(B).free,CARGO_TARGET_DIR=str(B/'NJC_target'),no_key_operations=True),indent=1)+'\n')
print(json.dumps(dict(status='PASS',modules=len(selected),closure_files=len(closure),export_bytes=sum(r['bytes'] for r in exports),NIU_seed_bytes=sum(r['bytes'] for r in imported))))
