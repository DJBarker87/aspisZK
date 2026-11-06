"""Read-only selected-object pinning and a small retained private export."""
from pathlib import Path
import os,json,hashlib,sys,shutil
B=Path(__file__).resolve().parent;cfg=json.loads((B/sys.argv[1]).read_text());roots=cfg['env']['LEAN_PATH'].split(':')
def pin(p):return dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
gate=json.loads((B/'NJF_L044.json').read_text())
for old in gate['deps_fingerprint']['selected_objects'].values():assert pin(Path(old['path']))['sha256']==old['sha256'],old['path']
seed=json.loads((B/'NJF_SEED.json').read_text())
for rel,old in seed['files'].items():assert pin(B/rel)['sha256']==old['sha256'],rel
scan=[json.loads(x)for x in(B/'NJF_final_audit/NJF_LOADED_scan.jsonl').read_text().splitlines()]
assert len(scan)==15195 and all(not x['dangling'] and not x['duplicate_owners'] and x['imports_match'] for x in scan)
selected=[];modules=[]
for row in scan:
 name=row['module'];rel=name.replace('.','/')+'.olean'
 p=next((Path(root)/rel for root in roots if (Path(root)/rel).is_file()),None);assert p is not None,name
 files=[p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]
 chosen=[]
 for q in files:
  if q.is_file():
   info=pin(q);info['module']=name;selected.append(info);chosen.append(str(q))
 modules.append(dict(module=name,files=chosen))
D=B/'NJF_retained_pins';D.mkdir(exist_ok=True);chunks=[]
for start in range(0,len(selected),4000):
 p=D/f'NJF_objects_{start//4000:02}.jsonl';p.write_text(''.join(json.dumps(x)+'\n'for x in selected[start:start+4000]));chunks.append(pin(p))
p=D/'NJF_selected_modules.jsonl';p.write_text(''.join(json.dumps(x)+'\n'for x in modules));chunks.append(pin(p))
# New semantic modules only; audit executables remain retained in NJF_native.
export=B/'NJF_exports_20261107/objects';export.mkdir(parents=True,exist_ok=True);exports={}
for row in modules:
 if not row['module'].startswith('NJF_'):continue
 for name in row['files']:
  p=Path(name);dst=export/p.name;shutil.copy2(p,dst);exports[p.name]=pin(dst)
(B/'NJF_EXPORT.json').write_text(json.dumps(dict(directory=str(export),files=exports,bytes=sum(x['bytes']for x in exports.values())),indent=2)+'\n')
# Import hashes for the immutable predecessor Rust/source seeds, read once.
P=Path('/home/dombarker/project-offloads/codex-cx-slice-d-pair7-20261107');imports=[]
for stem in ['NIW_src','NIW_target']:
 files=[pin(p)for p in sorted((P/stem).rglob('*'))if p.is_file()]
 imports.append(dict(source=str(P/stem),files=files,bytes=sum(x['bytes']for x in files)))
(B/'NJF_IMPORTED_CACHE_HASHES.json').write_text(json.dumps(dict(read_only=True,imports=imports),separators=(',',':'))+'\n')
tools={}
for name in [B/'S2W_run_host.py',B/'S2W_lean_host.py',Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'),Path('/home/dombarker/.kani/kani-0.67.0/bin/kani-driver'),Path('/home/dombarker/.cargo/bin/cargo-kani')]:
 if name.is_file():tools[str(name)]=pin(name)
for p in Path('/home/dombarker/.kani/kani-0.67.0/bin').iterdir():
 if p.is_file() and p.name in ['kani-compiler','cbmc','goto-instrument','goto-cc']:tools[str(p)]=pin(p)
solver=[]
for p in (B/'NJF_tmp').rglob('*'):
 if p.is_file() and (p.name.startswith('external-sat') or p.name.startswith('smt2_dec_problem')):
  solver.append(pin(p));p.unlink()
result=dict(workspace=str(B),CARGO_TARGET_DIR=cfg['env']['CARGO_TARGET_DIR'],lean_path=roots,modules=len(modules),selected_files=len(selected),selected_bytes=sum(x['bytes']for x in selected),pin_chunks=chunks,aeneas_actual_files=[x for x in selected if '/Aeneas/'in x['path'] or '/AeneasMeta/'in x['path'] or Path(x['path']).name in ['Aeneas.olean','AeneasMeta.olean']],tools=tools,seed_bytes=seed['seed_bytes'],seed_hashes_rechecked=True,export=str(export),solver_temporary_removed=solver,caches_deleted=False,free_bytes=shutil.disk_usage(B).free,first_audit='NJF_L041 historical stdout/receipt retained; final per-module scan snapshot is NJF_L044/audit_outputs')
(B/'NJF_RETENTION.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
assert all(p.stat().st_size<=20*1024*1024 for p in [B/'NJF_RETENTION.json',B/'NJF_IMPORTED_CACHE_HASHES.json',*D.iterdir()]),'split oversized metadata before commit'
print(json.dumps(dict(modules=len(modules),selected_files=len(selected),export_files=len(exports),export_bytes=sum(x['bytes']for x in exports.values()),free_bytes=result['free_bytes'])))
