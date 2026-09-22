#!/usr/bin/env python3
"""Bounded Linux scope only. Build R21 isolated arithmetic pilots.

No deployment, RPC, wallet, or fixture generation. Unchanged cached toolchain.
"""
import argparse,hashlib,json,os,subprocess
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--stage',type=Path,required=True)
p.add_argument('--mode',choices=['primary','diagnostic'],required=True)
p.add_argument('--omit-opening-reference',action='store_true')
a=p.parse_args();root=a.stage.resolve()
assert root.name.startswith('aspis-r21-') and not (root/'.git').exists()
meta=json.loads((root/'r18-stage.json').read_text())
assert 'r21_circuit' in meta and meta['r21_circuit']['full_aspis_verifier'] is False
assert meta['compact_primary']
assert meta['current_T_unchanged'] or meta.get('basis_profile')=='minimum-support-163'
for name,expected in meta['files'].items():
    assert hashlib.sha256((root/name).read_bytes()).hexdigest()==expected,name
probe=json.loads((root/'r17-sbf-probe.json').read_text())
ex=root/'docs/research/v8-no-work-100-20260907/experiments'
# Compare the source constructor to every frozen SBF map entry before building.
env=dict(os.environ)
env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',NO_DNA='1',
    CARGO_TARGET_DIR='/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz/docs/research/v8-no-work-100-20260907/experiments/performance-host/target')
for k in ['RUSTFLAGS','RUSTC']:env.pop(k,None)
actual=subprocess.check_output(['/home/dombarker/.cargo/bin/cargo','run','--offline','--locked',
    '--release','--jobs','2','--manifest-path',str(ex/'performance-host/Cargo.toml'),
    '--bin','r17-export-basis'],env=env,cwd=root)
assert actual==(ex/'r17_basis_tables.rs').read_bytes()
print('PASS all 1024 source permutation and inactive entries match SBF table',flush=True)
out=root/('sbf-'+a.mode);assert not out.exists()
if a.omit_opening_reference:
    assert meta.get('r19_opening'), 'source adapter required'
    gate=(root/'opening-gate.log').read_text()
    assert 'R19_OPENING source_arbitrary_authenticated=32' in gate and 'Exit status: 0' in gate, 'focused actual-source gate required'
    assert a.mode=='primary', 'diagnostic must retain reference'
extra=' --cfg r19_no_opening_reference' if a.omit_opening_reference else ''
env.update(PATH='/home/dombarker/.cargo/bin:/home/dombarker/.local/share/solana/install/active_release/bin:/usr/bin:/bin',
    RUSTC='/home/dombarker/.cache/solana/v1.54/platform-tools/rust/bin/rustc',
    RUSTFLAGS=probe['rustflags']+(' --cfg r18_primary_only' if a.mode=='primary' else '')+extra,
    CARGO_TARGET_DIR='/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz/docs/research/v8-no-work-100-20260907/experiments/performance-sbf/target')
cmd=['/usr/bin/time','-v','/home/dombarker/.local/share/solana/install/active_release/bin/cargo-build-sbf',
    '--offline','--skip-tools-install','--no-rustup-override','--tools-version','v1.54',
    '--jobs','2','--features',probe['features'],'--manifest-path',str(root/probe['manifest']),
    '--sbf-out-dir',str(out)]
proc=subprocess.Popen(cmd,env=env,cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
frame=False
for line in proc.stdout:
    print(line,end='',flush=True)
    frame |= 'overflows the maximum allowed frame' in line or ('Stack offset' in line and 'exceeded' in line)
code=proc.wait()
if frame:print('FAIL: frame diagnostic rejects this ELF',flush=True)
raise SystemExit(code or int(frame))
