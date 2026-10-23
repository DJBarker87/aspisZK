#!/usr/bin/env python3
"""Retain source-only UF experiments, including excluded failures."""
from pathlib import Path
import hashlib, json, shutil, tarfile
H = Path('/home/dombarker/project-offloads/s126-real-sdk-20261021')
O = H/'s1-claim-uf-export-v2'
O.mkdir(exist_ok=False)
def copy(p, dest):
    dest.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(p, dest)
tags = [
    's1-original-point-fission-v1', 's1-original-point-uf-v1',
    's1-original-point-pure-push-v1',
    's1-uf-positive-v1', 's1-uf-negative-v1',
    's1-uf-rust-positive-v1', 's1-uf-rust-positive-v2', 's1-uf-rust-negative-v1',
    's1-uf-push-positive-v1', 's1-uf-push-negative-v1',
    's1-uf-push-ssa-positive-v1', 's1-uf-push-ssa-negative-v1',
    's1-original-point-pure-push-ssa-v1',
    's1-original-point-replay-v1', 's1-original-point-replay-v2', 's1-original-point-replay-accepted-v1',
] + [f's1-claim-owned-nested-{phase}-v{v}' for v in range(1,8) for phase in ['charon','aeneas']]
for tag in tags:
    receipt = H/'receipts'/tag
    assert (receipt/'receipt.json').is_file(), ('not terminal', tag)
    for p in receipt.iterdir():
        if p.is_file() and p.suffix in ['.json', '.log']:
            copy(p, O/'attempts'/tag/p.name)
    for suffix in ['input', 'admission', 'dependency-postcheck', 'all-local-before', 'all-local-after']:
        p = H/(tag+'-'+suffix+'.json')
        if p.is_file():
            copy(p, O/'attempts'/tag/(suffix+'.json'))
for name in ['aspis-s1-claim-fission-point-v2', 'aspis-s1-claim-uf-v1',
             'aspis-s1-claim-uf-v2', 'aspis-s1-claim-uf-v4', 's1-uf-preflight-v1'] + [f's1-claim-owned-nested-v{v}' for v in range(1,8)] + [f'aspis-s1-claim-replay-v{v}' for v in range(1,4)]:
    root = H/name
    for p in root.rglob('*'):
        if not p.is_file() or any(x in ['target', '.git'] for x in p.relative_to(root).parts):
            continue
        if p.suffix in ['.rs', '.toml', '.lock', '.json', '.c', '.h', '.lean']:
            copy(p, O/'inputs'/name/p.relative_to(root))
for name in ['s1-run-uf-host.py', 's1-run-uf-ssa-host.py', 's1-run-fission-point-host.py', 's1-run-replay-host.py', 'extract-claim-owned-nested-host.py', 'extract-claim-owned-arrays-host.py', 'extract-claim-owned-scalar-host.py', 'extract-claim-owned-push-host.py', 'extract-claim-owned-frame-host.py', 'extract-claim-owned-sum-host.py', 'extract-claim-owned-sum-borrow-host.py']:
    p = H/name
    if p.is_file():
        copy(p, O/'runners'/name)
files = {str(p.relative_to(O)): hashlib.sha256(p.read_bytes()).hexdigest()
         for p in sorted(O.rglob('*')) if p.is_file()}
(O/'manifest.json').write_text(json.dumps(dict(
    schema='focused-extractor-proof-packet-v1', files=files,
    qualification='Pure numeric leaf interpretations only; source/control experiments are not actual arithmetic/SDK/source closure. Failed and timed-out attempts carry no semantic credit.'), indent=2)+'\n')
with tarfile.open(str(O)+'.tar.gz', 'w:gz') as t:
    for p in O.rglob('*'):
        if p.is_file():
            t.add(p, arcname=str(p.relative_to(O)))
print(json.dumps(dict(files=len(files), archive=str(O)+'.tar.gz')))
