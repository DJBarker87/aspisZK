from pathlib import Path
import hashlib,json,shutil
B=Path('/home/dombarker/project-offloads/codex-cx-leaf-p6-7-20261027')
manifest={};totals={}
for name in ['LPg_target','LPg_objects']:
 p=B/name;items={}
 if p.exists():
  for f in p.rglob('*'):
   if f.is_file():
    h=hashlib.sha256()
    with f.open('rb') as handle:
     for block in iter(lambda:handle.read(1024*1024),b''):h.update(block)
    items[str(f.relative_to(p))]={'sha256':h.hexdigest(),'bytes':f.stat().st_size}
 manifest[name]=items;totals[name]={'files':len(items),'bytes':sum(x['bytes'] for x in items.values())}
(B/'LPg_CACHE_HASHES.json').write_text(json.dumps(manifest,indent=2)+'\n')
# Cadical is in-process; these runs did not request external solver file emission.
left=[str(p) for pattern in ['external-sat*.cnf','smt2_dec_problem*'] for p in Path('/tmp').glob(pattern)]
for name in ['LPg_target','LPg_objects']:
 p=B/name
 if p.exists():shutil.rmtree(p)
out={'removed_compiled_caches':totals,'remaining_tmp_solver_candidates':left,'tmp_deletion':'none: no attributable own external-solver files; no other job files touched','retained':'LPg_src, proof sources, receipts, shared SInt2 objects and all wallet/account keys','process_check':'No LPg prover/solver may be running before this cleanup','cache_hashes':'LPg_CACHE_HASHES.json'}
(B/'LPg_CLEANUP.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
