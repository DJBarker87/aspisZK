#!/usr/bin/env python3
"""Public extraction/proof receipts only; never collect private fixtures/keys."""
import argparse, hashlib, json, shutil, subprocess
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
assert not a.output.exists();a.output.mkdir(parents=True)
base=Path('/home/dombarker/project-offloads')
def copy(s,d):d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(s,d)
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
for name,suffix in [('missing-build','a'),('opaque-map-err','b'),('broad-result','c'),('selected','d')]:
    folder=base/f'aspis-r72-sampler-20260929-{suffix}'
    for f in folder.iterdir():
        if f.is_file() and f.suffix in ['.json','.log','.py']:
            copy(f,a.output/name/f.name)
    if suffix in ['b','d']:
        for f in (folder/'generated').rglob('*'):
            if f.is_file():copy(f,a.output/name/'generated'/f.relative_to(folder/'generated'))
    if suffix=='d':
        copy(folder/'R72Sampler.llbc',a.output/name/'R72Sampler.llbc')
        for f in (folder/'source').rglob('*'):
            if f.is_file():copy(f,a.output/name/'source'/f.relative_to(folder/'source'))
for name,folder in [('final','aspis-r72-final-20260929-a'),
    ('generated-missing','aspis-r72-generated-20260929-a'),('generated','aspis-r72-generated-20260929-b'),
    ('outer-failed','aspis-r72-outer-20260929-a'),('outer','aspis-r72-outer-20260929-b')]:
    for f in (base/folder).iterdir():
        if f.is_file() and f.suffix in ['.json','.log']:copy(f,a.output/name/f.name)
deps=json.loads((a.output/'final/dependency-pins.json').read_text())
for path,h in deps.items():assert sha(Path(path))==h,path
runtime=base/'v7-tag73-challenge-qm31-source-20260825-work/toolchain/aeneas-full/backends/lean'
copy(runtime/'Aeneas/Std/Core/Fmt.lean',a.output/'runtime/CoreFmt.lean')
sysroot=Path(subprocess.check_output(
    ['/home/dombarker/.cargo/bin/rustup','run','nightly-2026-06-01','rustc','--print','sysroot'],text=True).strip())
copy(sysroot/'lib/rustlib/src/rust/library/core/src/result.rs',a.output/'stdlib/result.rs')
(a.output/'collection.json').write_text(json.dumps({'dependency_pins_verified':len(deps),
    'private_fixtures_collected':False,'wallet_keys_collected':False},indent=2)+'\n')
print(json.dumps({'files':sum(f.is_file()for f in a.output.rglob('*'))}))
