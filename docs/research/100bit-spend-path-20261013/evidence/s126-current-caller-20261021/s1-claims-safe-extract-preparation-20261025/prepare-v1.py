#!/usr/bin/env python3
"""Prepare exact source-only candidate extraction inputs. Never executes tools/SSH."""
from pathlib import Path
import argparse,hashlib,json,os,subprocess
R=Path(__file__).resolve().parents[2]
B=R/'docs/research/100bit-spend-path-20261013'
E=B/'evidence/s126-current-caller-20261021'
C=B/'rust-candidates/s1-claims-safe-storage-20261025'
parser=argparse.ArgumentParser();parser.add_argument('--out',required=True);args=parser.parse_args()
O=Path(args.out);O.mkdir(mode=0o700,parents=False,exist_ok=False)
freeze='25866ec331cc7ce27dd9956609c11d32fa8fa58a'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
blob=lambda path:subprocess.check_output(['git','show',freeze+':'+path],cwd=R)
pins=[]
def put(rel,data,origin):
    p=O/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
    pins.append(dict(path=rel,sha256=sha(p),**origin))
base=json.loads((E/'s1-init-local-20261025/source-binding.json').read_text())
for row in base['native_source_files']:
    if not row['path'].startswith('core-workspace/'):continue
    data=blob(row['source']);assert hashlib.sha256(data).hexdigest()==row['sha256']
    put(row['path'],data,dict(revision=freeze,source=row['source']))
put('core-workspace/Cargo.toml',b'[workspace]\nmembers=["crates/aspis-core"]\nresolver="2"\n[workspace.package]\nedition="2021"\nlicense="MIT OR Apache-2.0"\nversion="0.1.0"\n',dict(kind='Explicit frozen effective workspace metadata, same as checked local typecheck'))
for name in ['r1_wire.rs','sampler.rs']:
    source='crates/aspis-r1-cost-probe/src/'+name
    put('reference/src/'+name,blob(source),dict(revision=freeze,source=source))
body=(C/'claims.rs').read_bytes()
put('reference/src/candidate_claims.rs',b'use crate::r1_wire::{Prefix,Error};\nuse alloc::boxed::Box;\nuse aspis_core::field::QM31;\n'+body,dict(kind='Exact typechecked candidate body plus imports; no visibility/body rewrite'))
put('reference/src/lib.rs',b'#![no_std]\nextern crate alloc;\npub mod sampler;\npub mod r1_wire;\nmod candidate_claims;\n',dict(kind='Extraction root only; full real wire/field/error carriers'))
manifest='''[package]
name="aspis-r1-cost-probe"
version="0.1.0"
edition="2021"
[workspace]
[features]
default=["private-leaf-salts"]
private-leaf-salts=[]
prover=[]
r1p-check=[]
[dependencies]
aspis-core={path="../core-workspace/crates/aspis-core",features=["r0"]}
[profile.release]
opt-level=3
overflow-checks=true
[profile.dev]
opt-level=3
overflow-checks=true
[profile.dev.build-override]
opt-level=3
'''
put('reference/Cargo.toml',manifest.encode(),dict(kind='Same two-package focused dependency graph; explicit profile and path relocation'))
put('reference/Cargo.lock',(E/'s1-init-local-20261025/original-min/Cargo.lock').read_bytes(),dict(kind='Exact retained two-package checked lock'))
H='/home/dombarker/project-offloads/s126-real-sdk-20261021'
host=H+'/s1-claims-safe-extract-v1-20261025'
charon='/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon'
aeneas='/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static'
cmd=[charon,'cargo','--preset','aeneas','--mir','built','--sysroot','default','--opaque','crate',
    '--start-from','crate::candidate_claims::claims','--include','crate::candidate_claims::claims',
    '--include','crate::r1_wire::Prefix','--include','crate::r1_wire::Error',
    '--include','aspis_core::r0::heap::filled','--include','aspis_core::r0::Error',
    '--dest-file',host+'/ClaimsSafe.llbc','--','--manifest-path',host+'/reference/Cargo.toml',
    '--locked','--offline','--release','--lib','--jobs','1']
translate=[aeneas,'-sequential','-no-progress-bar','-abort-on-error','-print-error-emitters',
    '-loops-no-rec','-backend','lean','-namespace','AspisS1ClaimsSafeSource','-dest',host+'/generated',
    '-subdir','AspisS1ClaimsSafeSource','-split-files','-emit-json',host+'/ClaimsSafe.llbc']
old=json.loads((E/'s1-claims-row-step-20261024/charon/input.json').read_text()) if (E/'s1-claims-row-step-20261024/charon/input.json').exists() else None
plan=dict(schema='focused-extractor-proof-packet-v1',status='PREPARED_NOT_RUN',execution_enabled=False,
    source_freeze=freeze,candidate_binding=json.loads((C/'source-binding.json').read_text()),
    charon_command=cmd,aeneas_command=translate,source_files=pins,
    host_directory=host,expected_environment=dict(RUSTUP_TOOLCHAIN='nightly-2026-06-01',
    CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=H+'/owned-charon-target',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true'),
    expected_time='Warm focused Charon compilation/extraction of two-package source, then small Aeneas translation; no certificate generation/SAT/ELF/package replay.',
    proposed_scope=dict(MemoryHigh=1536*2**20,MemoryMax=2*2**30,MemorySwapMax=0,TasksMax=64),
    prerequisites=['Fresh reviewed complete host admission covering exactly this extraction; metadata-only GO is insufficient.',
        'Fresh before/after exact tool/runtime/source/import pins and no-writer private-cache check; old receipts are historical references only.',
        'One shared host lock, separate capped Charon/Aeneas phases, aggregate RSS/progress monitoring; no unchanged cap increase or cold rebuild.',
        'Charon LLBC has_errors false before translation; inspect any external templates without importing custom axioms.',
        'Smallest generated Lean target, then source body/Std/carrier/decoder/allocator proof installation and axioms audit; no automatic candidate adoption.'],
    remaining=['Native frozen/candidate all-outcome equivalence including allocation/error/drop/effects or separately reviewed replacement-source refinement.',
        'Concrete caller installation and mask/terminal obligations; complete release/CU/stack/two-transaction and source/artifact re-pin.'],
    compiler_launched=False,verification_launched=False,host_SSH_operations=0,print_axioms='N/A: source-only preparation')
put('disabled-run.py',b'raise SystemExit("DISABLED: prepared source only; fresh reviewed host admission and pins required before any extraction")\n',dict(kind='Fail-closed marker, no compiler/extractor invocation'))
plan['source_files']=pins
(O/'plan.json').write_text(json.dumps(plan,indent=2)+'\n')
print(json.dumps(dict(status=plan['status'],files=len(pins),directory=str(O),plan_sha256=sha(O/'plan.json'))))
