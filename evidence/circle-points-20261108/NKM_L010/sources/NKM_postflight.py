from pathlib import Path
import os,json,hashlib,lzma,shutil
B=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
config=json.loads((B/'NKM_L050.json').read_text());roots=config['env']['LEAN_PATH'].split(':')+[config['env']['LEAN_SYSROOT']+'/lib/lean']
scan=[json.loads(l)for l in(B/'NKM_LOADED_scan.jsonl').read_text().splitlines()]
files={};missing=[]
for row in scan:
 rel=row['module'].replace('.','/')+'.olean';p=next((Path(root)/rel for root in roots if (Path(root)/rel).is_file()),None)
 if p is None:missing.append(row['module']);continue
 for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if q.is_file():files[str(q)]=dict(path=str(q),sha256=sha(q),bytes=q.stat().st_size,module=row['module'])
assert not missing,missing
seed=json.loads(lzma.decompress((B/'NKM_CACHE_IMPORTS.json.xz').read_bytes()));seed_errors=[r['destination']for r in seed['files']if sha(Path(r['destination']))!=r['sha256']];assert not seed_errors
lib={}
for p in B.glob('NKM_L[0-9][0-9][0-9].json'):
 x=json.loads(p.read_text())
 for n,r in x.get('deps_fingerprint',{}).get('selected_objects',{}).items():
  if '/Aeneas' in n:
   if n in lib:assert lib[n]['sha256']==r['sha256'],('library pin changed across attempts',n)
   lib[n]=r
lib_errors=[n for n,r in lib.items()if sha(Path(n))!=r['sha256']];assert not lib_errors
raw=json.dumps(dict(files=files,selected_order=roots),sort_keys=True).encode();(B/'NKM_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw,preset=6));(B/'NKM_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
# Frozen-source and cfg-only overlay validation, plus final KMX/lock identity.
S=B/'NKM_workspace';pins={**json.loads((B/'NKM_FROZEN_FILE_PINS.json').read_text()),**json.loads((B/'NKM_SOURCE_PINS.json').read_text())};errors=[n for n,h in pins.items()if sha(S/n)!=h];assert not errors,errors
# Remove only own failed-solver transient files, after all native runs are terminal.
removed=[]
for p in (B/'NKM_tmp').rglob('*'):
 if p.is_file()and(p.name.startswith('external-sat')or p.name.startswith('smt2_dec_problem')):
  removed.append(dict(path=str(p),bytes=p.stat().st_size));p.unlink()
size=sum(p.stat().st_size for p in B.rglob('*')if p.is_file());assert size<20_000_000_000,size
summary=dict(closure_files=len(files),closure_modules=len(scan),closure_bytes=sum(r['bytes']for r in files.values()),Aeneas_files_rehashed=len(lib),Aeneas_unchanged=True,seed_files=len(seed['files']),seed_bytes=seed['bytes'],seed_unchanged=True,source_files_checked=len(pins),source_unchanged=True,lock_sha256=sha(S/'Cargo.lock'),own_workspace_bytes=size,own_writes_limit=20_000_000_000,free_bytes=shutil.disk_usage(B).free,solver_transients_removed=removed,cache_retained=True,CARGO_TARGET_DIR=str(B/'NKM_target'))
(B/'NKM_POSTFLIGHT.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary))
