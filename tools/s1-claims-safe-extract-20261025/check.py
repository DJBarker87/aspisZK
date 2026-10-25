#!/usr/bin/env python3
"""Verify prepared source, not extraction/admission/proof or adoption."""
from pathlib import Path
import argparse,hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013'
P=B/'evidence/s126-current-caller-20261021/s1-claims-safe-extract-preparation-20261025'
parser=argparse.ArgumentParser();parser.add_argument('--released',action='store_true');args=parser.parse_args()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((P/'manifest.json').read_text())
for rel,h in m['files'].items():assert sha(R/rel)==h,rel
d=json.loads((P/'plan-v2.json').read_text());release=json.loads((P/'release.json').read_text())
assert d['status']=='PREPARED_NOT_RUN' and d['execution_enabled'] is False
assert d['compiler_launched'] is False and d['verification_launched'] is False and d['host_SSH_operations']==0
assert d['proposed_scope']==dict(MemoryHigh=1536*2**20,MemoryMax=2*2**30,MemorySwapMax=0,TasksMax=64)
assert '--start-from' in d['charon_command'] and '--release' in d['charon_command']
assert 'crate::r1_wire::Prefix::validated_record' in d['charon_command']
assert 'crate::r1_wire::Prefix::record' in d['charon_command']
for row in d['source_files']:
    if 'revision' in row:
        data=subprocess.check_output(['git','show',row['revision']+':'+row['source']],cwd=R)
        assert hashlib.sha256(data).hexdigest()==row['sha256']
if args.released:
    O=Path(release['path'])
    assert {str(p.relative_to(O))for p in O.rglob('*')if p.is_file()}==set(release['files'])
    for rel,h in release['files'].items():assert sha(O/rel)==h,rel
    for p in [O,*O.rglob('*')]:assert p.stat().st_mode & 0o222==0
    assert sha(O/'plan.json')==release['plan_sha256']
    for row in d['source_files']:assert sha(O/row['path'])==row['sha256']
    body=(B/'rust-candidates/s1-claims-safe-storage-20261025/claims.rs').read_text()
    assert (O/'reference/src/candidate_claims.rs').read_text()=='use crate::r1_wire::{Prefix,Error};\nuse alloc::boxed::Box;\nuse aspis_core::field::QM31;\n'+body
    assert (O/'preparation.py').read_bytes()==(R/'tools/s1-claims-safe-extract-20261025/prepare.py').read_bytes()
    marker=(O/'disabled-run.py').read_text()
    assert marker=='raise SystemExit("DISABLED: prepared source only; fresh reviewed host admission and pins required before any extraction")\n'
print(f'PASS {len(d["source_files"])} prepared source pins; source release checked={args.released}; extraction/host authority/proof/adoption NOT established')
