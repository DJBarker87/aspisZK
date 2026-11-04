"""Export private objects, inventory retained cache, remove only own rebuildable outputs."""
from pathlib import Path
import json,hashlib,lzma,shutil,subprocess
P=Path('/home/dombarker/project-offloads');B=P/'codex-cx-slice-d-field2-20261104';C=P/'codex-cx-slice-d-field2-cache-20261104'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb')as f:
  for block in iter(lambda:f.read(1048576),b''):h.update(block)
 return h.hexdigest()
exports=[]
D=C/'NGA_exports_20261104';D.mkdir(exist_ok=True)
for p in (B/'NGA_objects').rglob('*'):
 if not p.is_file():continue
 q=D/p.relative_to(B/'NGA_objects');q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
 exports.append(dict(source=str(p),path=str(q),sha256=sha(q),bytes=q.stat().st_size))
p=B/'NGA_native/NGA_Driver';q=C/'NGA_native_20261104/NGA_Driver';q.parent.mkdir(exist_ok=True);shutil.copyfile(p,q);q.chmod(p.stat().st_mode)
exports.append(dict(source=str(p),path=str(q),sha256=sha(q),bytes=q.stat().st_size))
# Complete requested cache seeds with only named leaf/pilot objects; never a whole-cache copy.
extra=[]
for folder,names in [('codex-cx-leaf-cache-20261027',['LPe_MersenneReduction.olean','LPf_BaseMultiply.olean','LPf_CoreReduction.olean']),('codex-cx-cpilot-cache-20261028',['NCO_objects'])]:
 for name in names:
  src=P/folder/name
  files=list(src.rglob('*'))if src.is_dir()else[src]
  for p in files:
   if not p.is_file():continue
   q=C/'NGA_seed_extras'/folder/p.relative_to(P/folder);q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
   extra.append(dict(source=str(p),path=str(q),sha256=sha(q),bytes=q.stat().st_size,selected=False))
# Inventory even the excluded partial first copy without loading objects or executing proofs.
rows=[]
for p in sorted(C.rglob('*')):
 if p.is_file():rows.append(dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size))
raw=json.dumps(dict(cache=str(C),files=rows),sort_keys=True).encode();(B/'NGA_CACHE_INVENTORY.json.xz').write_bytes(lzma.compress(raw,preset=6));(B/'NGA_CACHE_INVENTORY.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
lock=B/'NGA_src/Cargo.lock';assert sha(lock)=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
removed=[]
for name in ['NGA_target','NGA_ref_target','NGA_objects','NGA_native']:
 p=B/name
 if p.exists():shutil.rmtree(p);removed.append(str(p))
# Only private generated temporary files; no keys or other workers' paths are touched.
tmp=B/'NGA_tmp'
if tmp.exists():
 for p in tmp.iterdir():
  if p.is_file()and(p.name.startswith('external-sat')or p.name.startswith('smt2_dec_problem')):p.unlink();removed.append(str(p))
code='pgrep -af "S2W_run_host.py NGA_|lean.*NGA_generated|cbmc.*NGA_target" || true'
processes=subprocess.run(['bash','-c',code],capture_output=True,text=True).stdout
out=dict(workspace=str(B),cache=str(C),objects=exports,seed_extras=extra,cache_files=len(rows),cache_bytes=sum(x['bytes']for x in rows),cache_inventory_raw_sha256=hashlib.sha256(raw).hexdigest(),cache_deleted=False,removed_only_private_rebuildable=removed,scratch_lock_sha256=sha(lock),process_snapshot=processes,print_axioms='N/A: private export/inventory/cleanup; proof measurements in receipts')
(B/'NGA_CACHE_END.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(dict(exports=len(exports),cache_files=len(rows),cache_bytes=out['cache_bytes'],removed=removed)))
