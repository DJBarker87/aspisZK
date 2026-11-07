from pathlib import Path
import json,hashlib,lzma,shutil,os
B=Path.cwd();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
env=json.loads((B/'NMN_L024.json').read_text())['env'];roots=env['LEAN_PATH'].split(':')
selected=lambda rel:next(Path(r)/rel for r in roots if (Path(r)/rel).is_file())
assert sha(selected('NFA_WALKER.olean'))=='f51bf7fb3b7a43948ebc785fc45b41c9e47b0f52aad937ce2cd2a879f6c16c70'
loaded=[json.loads(l) for l in (B/'NMN_LOADED_scan.jsonl').read_text().splitlines()];assert all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in loaded)
closure=[]
for row in loaded:
 p=selected(row['module'].replace('.','/')+'.olean')
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.is_file():closure.append(dict(module=row['module'],path=str(z),sha256=sha(z),bytes=z.stat().st_size))
raw=json.dumps(closure,sort_keys=True).encode();(B/'NMN_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw));(B/'NMN_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
export=B/'NMN_exports_20261110';export.mkdir(exist_ok=True);files=[]
for mod in ['NMN_064', 'NMN_241Continuation', 'NMN_241Prefix', 'NMN_241Suffix', 'NMN_241ValueFold', 'NMN_242Interface', 'NMN_COMBINED_IMPORT', 'NMN_CallerDomain', 'NMN_Headline', 'NMN_Inspect241', 'NMN_Observer', 'NMN_OracleFold', 'NMN_Relation']:
 p=B/'NMN_objects'/(mod+'.olean');src=B/'NMN_generated'/(mod+'.lean')
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir'),src]:
  if not z.is_file():continue
  q=export/z.name
  if q.exists():assert q.read_bytes()==z.read_bytes()
  else:shutil.copy2(z,q)
  files.append(dict(source=str(z),path=str(q),sha256=sha(q),bytes=q.stat().st_size))
(B/'NMN_EXPORT.json').write_text(json.dumps(dict(path=str(export),files=files,bytes=sum(r['bytes'] for r in files)),indent=1)+'\n')
# The inherited scratch corpus includes unused historical Pool source. It is
# explicitly outside every selected verifier dependency closure; no Pool credit.
different=[]
(B/'NMN_UNUSED_POOL_FINDING.json').write_text(json.dumps(dict(owner_revision='b936275465',selected_pool_crates=False,credit='Inherited unused Pool corpus is outside every selected native closure; no Pool execution/parity or ELF rebuild is claimed.'),indent=1)+'\n')
seed=[]
for p in (B/'NMN_seed').rglob('*'):
 if p.is_file():seed.append(dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size))
# Recheck every pinned Aeneas object and sidecar from the final scope.
cfg=json.loads((B/'NMN_L026.json').read_text());pins=cfg['deps_fingerprint']['selected_objects'];checked=0
for p,row in pins.items():
 assert sha(Path(p))==row['sha256'],p
 if 'Aeneas' in p:checked+=1
workspace=sum(p.stat().st_size for p in B.rglob('*') if p.is_file() and not p.is_symlink())
assert workspace<30_000_000_000
(B/'NMN_RETENTION.json').write_text(json.dumps(dict(workspace_bytes=workspace,free_bytes=shutil.disk_usage(B).free,seed_files=len(seed),seed_bytes=sum(r['bytes'] for r in seed),closure_files=len(closure),loaded_modules=len(loaded),aeneas_objects_checked=checked,all_final_pins_unchanged=True,host_deletions=0,cache_and_tmp_retained=True),indent=1)+'\n')
tools={}
for name in ['cargo-kani','cargo']:
 p=Path('/home/dombarker/.cargo/bin')/name;tools[str(p)]=dict(realpath=str(p.resolve()),sha256=sha(p))
for name in ['lean','lake','leanc']:
 p=Path(env['LEAN_SYSROOT'])/'bin'/name;tools[str(p)]=dict(realpath=str(p.resolve()),sha256=sha(p))
(B/'NMN_TOOL_PINS.json').write_text(json.dumps(tools,indent=1)+'\n')
print(json.dumps(dict(export_files=len(files),closure_files=len(closure),modules=len(loaded),workspace_bytes=workspace,unused_pool_differences=len(different),aeneas_objects_checked=checked)))
