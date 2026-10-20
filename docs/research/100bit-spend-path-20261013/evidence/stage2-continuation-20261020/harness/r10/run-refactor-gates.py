#!/usr/bin/env python3
"""Serial refactor gates: stop on any nonzero receipt, including wrapper masks."""
import json, subprocess
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-stage2b-20261020')
for gate,receipt in [('program','gate-program-lib-inputs-complete'),('crate-default','gate-crate-default'),('crate-detail','gate-crate-detail'),('pool-default','gate-pool-default'),('pool-r1','gate-pool-r1-features'),('pool-all','gate-pool-all-features'),('pool-v7','gate-pool-v7-candidate'),('teeth','gate-teeth-inputs-complete'),('auth','gate-authenticated-tx2')]:
    print('START',gate,flush=True)
    subprocess.run(['sh',str(H/'harness-r10/gates.sh'),gate],check=True)
    r=json.loads((H/'receipts'/('r10-'+receipt)/'receipt.json').read_text())
    if r['exit_status']!=0: raise SystemExit(f'FAILED {gate}: {r}')
    print('PASS',gate,flush=True)
