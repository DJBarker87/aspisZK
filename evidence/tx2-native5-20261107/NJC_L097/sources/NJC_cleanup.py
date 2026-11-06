from pathlib import Path
import json,shutil
B=Path.cwd().resolve();assert B.name=='codex-cx-tx2-native5-20261107'
p=B/'NJC_target';before=sum(f.stat().st_size for f in p.rglob('*') if f.is_file()) if p.exists() else 0
if p.exists():shutil.rmtree(p)
# Sources, pinned caches and exports are retained. No key/account operations.
x=dict(status='PASS',removed=[str(p)],target_bytes_before=before,target_exists_after=p.exists(),free_bytes=shutil.disk_usage(B).free,retained=[str(B/'NJC_objects'),str(B/'NJC_src')],CARGO_TARGET_DIR=str(p),no_key_operations=True)
(B/'NJC_CLEANUP.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps(dict(status='PASS',removed_target_bytes=before,free_bytes=x['free_bytes'])))
