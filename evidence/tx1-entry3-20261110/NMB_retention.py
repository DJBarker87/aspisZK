"""Validate immutable source snapshots, selected Aeneas objects and copied seeds."""
from pathlib import Path
import json,hashlib,shutil,os
B=Path.cwd()
def sha(p):
 with p.open('rb')as f:return hashlib.file_digest(f,'sha256').hexdigest()
checked=0;ae={};receipts=[]
for p in B.glob('NMB_[LK][0-9][0-9][0-9]/receipt.json'):
 r=json.loads(p.read_text());receipts.append(r)
 for n,h in r['source_hashes'].items():
  q=p.parent/'sources'/n;assert q.is_file(),str(q);assert sha(q)==h,str(q);checked+=1
 for n,v in r.get('deps_fingerprint',{}).get('selected_objects',{}).items():
  if '/Aeneas' in n:
   assert n not in ae or ae[n]==v['sha256'],n;ae[n]=v['sha256']
for n,h in ae.items():assert sha(Path(n))==h,n
seed=json.loads((B/'NMB_seed_inventory.json').read_text());seed_count=0
for row in seed['files']:
 assert sha(Path(row['destination']))==row['sha256'],row['destination']
 assert sha(Path(row['source']))==row['sha256'],row['source'];seed_count+=1
# Preserve every own source/object/target/TMPDIR; no cleanup is performed.
workspace=sum(p.stat().st_size for p in B.rglob('*')if p.is_file());assert workspace<30_000_000_000
free=shutil.disk_usage(B).free;assert free>=40_000_000_000
summary=dict(source_snapshots_checked=checked,completed_scope_receipts=len(receipts),stable_selected_aeneas_files=len(ae),copied_seed_files_checked=seed_count,workspace_bytes=workspace,free_bytes=free,target_retained=(B/'NMB_target').is_dir(),tmp_retained=(B/'NMB_tmp').is_dir(),deleted_files=0,all_checks=True)
(B/'NMB_RETENTION.json').write_text(json.dumps(summary,indent=1)+'\n');print(json.dumps(summary))
