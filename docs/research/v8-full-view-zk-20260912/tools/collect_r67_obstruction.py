#!/usr/bin/env python3
"""Collect exact rejected extraction evidence, never accept template axioms."""
import argparse, hashlib, json, shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
root=Path('/home/dombarker/project-offloads');out=a.output
assert not out.exists();out.mkdir(parents=True)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def copy(s,d):
    assert s.is_file() and 'keypair' not in str(s)
    d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(s,d)
for suffix,folder in [('a','extraction-failure'),('b','eta-extraction')]:
    stage=root/f'aspis-r67-extracted-20260929-{suffix}'
    for n in ['R67Circle.llbc','commands.json','environment.json','lock.log','extract.log','translate.log']:
        copy(stage/n,out/folder/n)
    for directory in ['source','generated','original']:
        for src in (stage/directory).rglob('*'):
            if src.is_file():copy(src,out/folder/src.relative_to(stage))
    for n in ['normalization.json','pins.json']:
        if (stage/n).exists():copy(stage/n,out/folder/n)
std=Path('/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src')
for rel in ['array/mod.rs','iter/traits/iterator.rs','iter/adapters/chain.rs','option.rs','slice/iter/macros.rs']:
    copy(std/rel,out/'stdlib-source'/rel)
tool=root/'aspis-v7-aeneas-source-unblock-20260830'
for name in ['SymbolicToPureTypes.ml','SymbolicToPureExpressions.ml']:
    copy(tool/'reconstruct.oJL55K/src/symbolic'/name,out/'translator-source'/name)
runtime=root/'v7-tag73-challenge-qm31-source-20260825-work/toolchain/aeneas-full/backends/lean'
copy(runtime/'Aeneas/Std/Core/Iter.lean',out/'runtime-source/Iter.lean')
record={'base_revision':'8de551b22484de15f0407f80d9257154043d3b04',
 'charon_sha256':sha(root/'ZK-v5-formal/toolchains/charon/bin/charon'),
 'aeneas_sha256':sha(tool/'aeneas-repro-r1'),
 'rust_std_source_root':str(std),'no_new_Lean_compilation':True,
 'accepted_as_source_proof':False,'runtime_changed':False}
(out/'collection.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'output':str(out),'files':sum(p.is_file() for p in out.rglob('*'))}))
