"""Read-only checks of the exact frozen scratch inputs and focused modules."""
from pathlib import Path
import json,hashlib,shutil
B=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((B/'NKK_SOURCE_PINS.json').read_text())
errors=[n for n,h in pins.items() if not (B/'NKK_src'/n).is_file() or sha(B/'NKK_src'/n)!=h]
assert not errors,errors
assert sha(B/'NKK_src/Cargo.lock')=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
modules=json.loads((B/'NKK_MODULES.json').read_text())+['NKK_COMBINED_IMPORT']
for m in modules:
 assert (B/'NKK_generated'/(m+'.lean')).is_file(),m
 assert (B/'NKK_objects'/(m+'.olean')).is_file(),m
report=dict(status='PASS',source_files=len(pins),source_errors=errors,lock_unchanged=True,modules=len(modules),free_bytes=shutil.disk_usage(B).free,cargo_target=str(B/'NKK_target'),shipped_files_modified=False)
(B/'NKK_SOURCE_VERIFICATION.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
