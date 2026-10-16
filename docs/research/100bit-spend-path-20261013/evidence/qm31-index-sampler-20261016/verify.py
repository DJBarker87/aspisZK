#!/usr/bin/env python3
"""Verify exact-cut/native receipts; does not rerun tests or claim refinement."""
import hashlib
import json
from pathlib import Path
import subprocess

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[4]
KIT=HERE.parents[1]/'tools/qm31-index-sampler-extraction-kit'
sha=lambda raw:hashlib.sha256(raw).hexdigest()
for line in (HERE/'SHA256SUMS').read_text().splitlines():
    digest,name=line.split('  ',1)
    assert sha((HERE/name).read_bytes())==digest,name
subprocess.run(['python3',str(KIT/'extract.py'),'--check'],check=True)
pins=json.loads((KIT/'source-pins.json').read_text())
for path,digest in pins['source_files'].items():
    assert sha(subprocess.check_output(['git','-C',str(REPO),'show',pins['source_revision']+':'+path]))==digest
archive=json.loads((HERE/'production-archive.json').read_text())
assert archive['source_revision']==pins['source_revision']
raw=subprocess.check_output(['git','-C',str(REPO),'archive','--format=tar',pins['source_revision'],
                             'Cargo.toml','Cargo.lock','.cargo','crates','programs',
                             'audit/poseidon-pair-probe/program','xtask'])
assert sha(raw)==archive['archive_sha256']
for label,runner in [('kit-native','run-host.py'),('production-native','run-native-crate.py')]:
    folder=HERE/'runs'/label
    receipt=json.loads((folder/'receipt.json').read_text())
    assert receipt['source_revision']==pins['source_revision']
    assert receipt['runner_sha256']==sha((KIT/runner).read_bytes())
    assert receipt['exit_status']==0 and receipt['swaps']==0
    assert receipt['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0'}
    assert '3 passed; 0 failed' in (folder/'stdout.log').read_text()
print('PASS: source cut, before-body equality, archive, native receipts and hashes; source refinement OPEN')
