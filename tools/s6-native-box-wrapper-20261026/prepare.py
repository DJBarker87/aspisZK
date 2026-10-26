#!/usr/bin/env python3
"""Pinned native decoder-wrapper fixture, actual SDK error type and child cut."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys
import tarfile
import tomllib

R=Path(__file__).resolve().parents[2];D=Path(__file__).parent
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';O=Path(sys.argv[1]).resolve()
sha=lambda b:hashlib.sha256(b).hexdigest()
subprocess.run([sys.executable,str(R/'tools/s6-native-getter-20261026/prepare.py'),str(O)],cwd=R,check=True,stdout=subprocess.DEVNULL)
binding=json.loads((O/'binding.json').read_text())
selected={
 'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs':['PoolV1PairForestTerminalFormatErrorV1'],
 'crates/aspis-statement/src/pool_v1/payment_relation.rs':['PoolV1PaymentStatementFormatError'],
 'crates/aspis-statement/src/pool_v1/pair_tree_profile.rs':['PoolV1PairLatePublicStatementErrorV1','PoolV1PairLiveSnapshotErrorV1'],
 'crates/aspis-statement/src/pool_v1/pair_terminal.rs':['PoolV1PairVerifierTransportErrorV1'],
 'crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs':['PoolV1PairForestAccountErrorV1'],
 'crates/aspis-statement/src/pool_v1/incremental_merkle.rs':['PoolV1TreeError'],
}
attribute='#[cfg_attr(kani, derive(kani::Arbitrary))]\n'
for path,names in selected.items():
    before=(O/path).read_text();after=before
    for name in names:
        marker='pub enum '+name
        matches=list(re.finditer(re.escape(marker)+r'\b',after));assert len(matches)==1
        pos=matches[0].start();after=after[:pos]+attribute+after[pos:]
    assert after.replace(attribute,'')==before
    (O/path).write_text(after)
(O/'harness/src/lib.rs').write_bytes((D/'proofs.rs').read_bytes())
p=O/'harness/Cargo.toml';s=p.read_text().replace('name = "s6-native-getter"','name = "s6-native-box-wrapper"')
s+='solana-program-error = {version = "=2.2.2", default-features = false}\n';p.write_text(s)
lock=subprocess.check_output(['git','show',REV+':Cargo.lock'],cwd=R)
(O/'Cargo.lock').write_bytes(lock)
env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2025-11-21-aarch64-apple-darwin',CARGO_NET_OFFLINE='true')
cargo=Path('/Users/dominic/.rustup/toolchains/nightly-2025-11-21-aarch64-apple-darwin/bin/cargo')
cmd=[str(cargo),'metadata','--manifest-path',str(O/'harness/Cargo.toml'),'--offline','--format-version','1']
q=subprocess.run(cmd,env=env,cwd=O,capture_output=True,text=True,timeout=30)
(O/'metadata.stderr.log').write_text(q.stderr)
assert q.returncode==0,q.stderr
metadata=json.loads(q.stdout)
frozen_lock=tomllib.loads(lock.decode())
expected={(p['name'],p['version']):p.get('checksum') for p in frozen_lock['package']}
def package_pins(name,version,path):
    checksum=expected[(name,version)]
    archive=Path.home()/'.cargo/registry/cache/index.crates.io-1949cf8c6b5b557f'/(name+'-'+version+'.crate')
    assert sha(archive.read_bytes())==checksum
    files={}
    with tarfile.open(archive) as t:
        for member in t.getmembers():
            if member.isdir():continue
            assert member.isfile()
            rel=Path(member.name).relative_to(name+'-'+version)
            value=t.extractfile(member).read()
            assert (path/rel).read_bytes()==value,(name,str(rel))
            files[str(rel)]=sha(value)
    return {'checksum':checksum,'files':files}
registry={}
for package in metadata['packages']:
    if package['source'] is None:continue
    path=Path(package['manifest_path']).parent
    registry[package['name']+'-'+package['version']]=package_pins(package['name'],package['version'],path)
assert 'solana-program-error-2.2.2' in registry
sdk=Path('/Users/dominic/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/solana-program-2.3.0')
checks=package_pins('solana-program','2.3.0',sdk)
assert checks['checksum']=='98eca145bd3545e2fbb07166e895370576e47a00a7d824e325390d33bf467210'
reexport=(sdk/'src/program_error.rs').read_bytes()
assert sha(reexport)==checks['files']['src/program_error.rs']
assert b'solana_program_error::ProgramError,' in reexport
(O/'sdk-reexport.rs').write_bytes(reexport)
(O/'registry-pins.json').write_text(json.dumps(registry,indent=2)+'\n')
files={str(p.relative_to(O)):sha(p.read_bytes()) for p in sorted(O.rglob('*')) if p.is_file() and p.name!='binding.json'}
binding.update(files=files,proof_only_arbitrary_derives=selected,derive_attribute=attribute,
               native_helper_file='programs/r1-cost-probe/src/r1_pool_adapter.rs',
               sdk_error_type='solana-program-error 2.2.2, same frozen solana-program 2.3.0 re-export',
               sdk_program_checksum=checks['checksum'],sdk_reexport_sha256=sha(reexport),
               copied_release_lock_sha256=sha(lock),resolved_lock_sha256=sha((O/'Cargo.lock').read_bytes()),
               registry_package_count=len(registry),child_boundary='one actual typed native decoder Result, complete FormatError and statement types',
               qualification='Exact release wrapper, Box::new/map_err/drop and native getters. Only decoder is cut; wrapper allocator remains Kani default. Full native fields/all decoder errors retained. Fixed1880-byte source-entry domain, all byte values. No SDK/account/decoder/runtime/artifact closure.')
(O/'binding.json').write_text(json.dumps(binding,indent=2)+'\n')
print(json.dumps({'workspace':str(O),'registry_packages':len(registry),'source_files':len(files),'error_type_derives':7}))
