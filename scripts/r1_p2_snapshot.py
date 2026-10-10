#!/usr/bin/env python3
"""UNPROVED P2 source snapshot, before each changed-source job."""
from pathlib import Path
import hashlib,json,subprocess
files=[]
for base in ['crates','programs','xtask','audit/poseidon-pair-probe/program']:
 files.extend(p for p in Path(base).rglob('*') if p.is_file() and p.suffix in ['.rs','.toml','.lock'])
files += [Path(p) for p in ['Cargo.toml','Cargo.lock','scripts/r1_p2_run.py','scripts/r1_p2_snapshot.py','scripts/v8_state_only_cu_record.py']]
m={'label':'UNPROVED COST PROBE P2','source_revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'files':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(files)}}
m['snapshot_sha256']=hashlib.sha256(json.dumps(m['files'],sort_keys=True).encode()).hexdigest()
Path('results/r1-precheck-20261010/source-manifest.json').write_text(json.dumps(m,indent=2)+'\n')
