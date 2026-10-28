from pathlib import Path
import json,hashlib,shutil
b=Path('/home/dombarker/project-offloads/codex-cx-native-cpilot2-20261028');cache=Path('/home/dombarker/project-offloads/codex-cx-cpilot2-cache-20261028')
def pin(p):return {'sha256':hashlib.file_digest(p.open('rb'),'sha256').hexdigest(),'bytes':p.stat().st_size}
procs=[]
for p in Path('/proc').iterdir():
 if not p.name.isdigit():continue
 try:
  args=(p/'cmdline').read_bytes().replace(b'\x00',b' ').decode(errors='replace')
  if str(b) in args and any(t in args for t in ['cargo-kani','cbmc ','charon-driver','bin/aeneas','bin/lean ','S2W_lean_host.py','S2W_run_host.py']):procs.append({'pid':p.name,'args':args})
 except (FileNotFoundError,PermissionError,ProcessLookupError):pass
assert not procs,procs
cachepins={str(p.relative_to(cache)):pin(p) for p in cache.rglob('*') if p.is_file()}
(b/'NCP_CACHE_END.json').write_text(json.dumps(cachepins,indent=2))
paths=['/home/dombarker/.cargo/bin/cargo-kani','/home/dombarker/.kani/kani-0.67.0/bin/kani-compiler','/home/dombarker/.kani/kani-0.67.0/bin/cbmc','/home/dombarker/.kani/kani-0.67.0/bin/goto-instrument','/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake']
tools={s:pin(Path(s)) for s in paths if Path(s).is_file()}
(b/'NCP_FINAL_TOOL_PINS.json').write_text(json.dumps(tools,indent=2))
# Final-cache artifact pins do not pretend to identify overwritten historical per-run artifacts.
art={str(p.relative_to(b)):pin(p) for p in (b/'NCP_target').rglob('*') if p.is_file() and (p.suffix=='.out' or p.name.endswith('.kani-metadata.json'))}
(b/'NCP_FINAL_GOTO_CACHE_PINS.json').write_text(json.dumps({'scope':'final cache state only; source/command pins are per-attempt','artifacts':art},indent=2))
removed=[];kept=[]
for n in ['NCP_target','NCP_extract_target','NCP_tmp']:
 p=b/n
 if not p.exists():continue
 files=[f for f in p.rglob('*') if f.is_file()]
 protected=[str(f) for f in files if f.name.endswith(('keypair.json','wallet.json'))]
 if protected:kept.append({'path':str(p),'reason':'retain possible task key files','files':protected});continue
 size=sum(f.stat().st_size for f in files);removed.append({'path':str(p),'files':len(files),'bytes':size});shutil.rmtree(p)
assert cache.exists()
x={'active_own_provers':procs,'removed_rebuildable_scratch':removed,'kept':kept,'private_cache_retained':str(cache),'private_cache_files':len(cachepins),'keys_or_wallet_operations':'none; cleanup preserves any directory containing a possible key file','final_tool_paths':len(tools),'final_artifacts_pinned':len(art)}
(b/'NCP_CLEANUP.json').write_text(json.dumps(x,indent=2));print(json.dumps(x))
