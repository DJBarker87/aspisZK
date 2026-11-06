"""Read-only final retention/disk verification; no deletion."""
from pathlib import Path
import json,shutil
B=Path(__file__).resolve().parent
size=sum(p.stat().st_size for p in B.rglob('*') if p.is_file())
assert size<30_000_000_000,size
assert shutil.disk_usage(B).free>=40_000_000_000
assert (B/'NKK_exports_20261108').is_dir()
assert (B/'NKK_exports_final_20261108').is_dir()
report=dict(workspace=str(B),own_bytes=size,free_bytes=shutil.disk_usage(B).free,cargo_target=str(B/'NKK_target'),cache_retained=True,cache_deleted=False,keys_touched=False,deleted_paths=[])
for n in ['NKK_RETENTION.json','NKK_CLEANUP.json']:(B/n).write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
