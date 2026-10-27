from pathlib import Path
import hashlib,json,shutil,subprocess
B=Path('/home/dombarker/project-offloads/codex-cx-leaf-p6-8-20261027')
ps=subprocess.check_output(['ps','-u','dombarker','-o','pid,comm,args'],text=True)
live=[l for l in ps.splitlines() if (' LPh_K' in l or ' LPh_L' in l or str(B/'LPh_target') in l) and ('S2W_' in l or 'cargo-kani' in l or 'cbmc ' in l) and 'bash -c' not in l]
assert not live,live
manifest={};totals={}
for name in ['LPh_target','LPh_objects','LPh_tmp']:
 p=B/name;items={}
 if p.exists():
  assert not list(p.rglob('*keypair*.json')),('retain possible task key',name)
  for f in p.rglob('*'):
   if f.is_file():
    h=hashlib.sha256()
    with f.open('rb') as stream:
     for block in iter(lambda:stream.read(1024*1024),b''):h.update(block)
    items[str(f.relative_to(p))]={'sha256':h.hexdigest(),'bytes':f.stat().st_size}
 manifest[name]=items;totals[name]={'files':len(items),'bytes':sum(x['bytes'] for x in items.values())}
(B/'LPh_CACHE_HASHES.json').write_text(json.dumps(manifest,indent=2)+'\n')
for name in ['LPh_target','LPh_objects','LPh_tmp']:
 p=B/name
 if p.exists():shutil.rmtree(p)
left=[{'path':str(p),'mtime':p.stat().st_mtime,'bytes':p.stat().st_size} for pattern in ['external-sat*.cnf','smt2_dec_problem*'] for p in Path('/tmp').glob(pattern)]
out={'removed_compiled_caches':totals,'own_live_provers':live,'shared_tmp_candidates_retained':left,'solver_tmp_policy':'Cadical is in-process; no external solver emission requested. Future diagnostic runs used own LPh_tmp, now hashed and removed. Unattributed/shared /tmp files retained.','retained':'LPh_src, all sources and per-attempt snapshots/receipts, complete K030 trace, shared SInt2/replay caches, all wallet/account keys','wallet_key_cleanup':'none performed','cache_hashes':'LPh_CACHE_HASHES.json'}
(B/'LPh_CLEANUP.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='shared_tmp_candidates_retained'}))
