#!/usr/bin/env python3
"""Hash exact build inputs before each capped job; no generated keys."""
import hashlib, json, subprocess
from pathlib import Path
root=Path(__file__).resolve().parent.parent
files={}
for folder in ['crates','programs','audit/poseidon-pair-probe/program','audit/r0-primitive-probe','xtask','tools/v8-state-only-cu-probe']:
    for p in (root/folder).rglob('*'):
        if p.is_file() and p.suffix in ['.rs','.toml','.lock'] and 'target' not in p.parts:
            files[str(p.relative_to(root))]=hashlib.sha256(p.read_bytes()).hexdigest()
for pattern in ['Cargo.*','scripts/r0_p1*.py','scripts/r0_re3_stack_audit.py','scripts/v8_state_only_cu_record.py']:
    for p in root.glob(pattern): files[str(p.relative_to(root))]=hashlib.sha256(p.read_bytes()).hexdigest()
out=root/'results/r0-cost-probe-20261009'
out.mkdir(parents=True,exist_ok=True)
record={'base_revision':'f1e5ca9de668110f80c548abe5e80b43f838099f','source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(), 'files':dict(sorted(files.items()))}
record['snapshot_sha256']=hashlib.sha256(json.dumps(record['files'],sort_keys=True).encode()).hexdigest()
(out/'source-manifest.json').write_text(json.dumps(record,indent=2)+'\n')
print(record['snapshot_sha256'])
