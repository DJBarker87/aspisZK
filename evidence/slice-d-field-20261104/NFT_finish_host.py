"""Own workspace export and rebuildable-target cleanup after all proof jobs exit."""
from pathlib import Path
import shutil,hashlib,json,subprocess,datetime
B=Path('/home/dombarker/project-offloads/codex-cx-slice-d-field-20261104')
C=Path('/home/dombarker/project-offloads/codex-cx-slice-d-field-cache-20261104')
export=C/'NFT_exports_20261104';export.mkdir(exist_ok=True)
pins=[]
for p in sorted((B/'NFT_objects').rglob('*')):
 if not p.is_file()or not p.relative_to(B/'NFT_objects').parts[0].startswith('NFT_'):continue
 dst=export/p.relative_to(B/'NFT_objects');dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,dst)
 a=hashlib.sha256(p.read_bytes()).hexdigest();assert a==hashlib.sha256(dst.read_bytes()).hexdigest()
 pins.append(dict(path=str(dst),sha256=a,bytes=p.stat().st_size))
removed=[]
for name in ['NFT_target','NFT_ref_target']:
 p=B/name
 if p.exists():
  assert p.parent==B and not p.is_symlink()
  size=sum(f.stat().st_size for f in p.rglob('*')if f.is_file());shutil.rmtree(p);removed.append(dict(path=str(p),bytes=size,reason='private rebuildable Rust target; proof jobs complete; no keys or source'))
# Timeout solver temporaries under our dedicated TMPDIR were already unlinked by tools.
assert not list((B/'NFT_tmp').iterdir())
out=dict(host='dombarker@100.108.41.90',workspace=str(B),cache=str(C),export=str(export),objects=pins,deleted_rebuildable_targets=removed,tmp_empty=True,cache_retained=True,time=datetime.datetime.now(datetime.timezone.utc).isoformat(),disk_free_bytes=shutil.disk_usage(B).free)
print(json.dumps(out,indent=1))
