#!/usr/bin/env python3
"""Freeze bounded diagnostics for the unresolved std array source boundary."""
from pathlib import Path
import hashlib,json,subprocess,sys

plan=json.loads(Path(sys.argv[1]).read_text())
root=Path(plan['workspace']);out=Path(plan['artifact_output'])
out.mkdir(parents=True,exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=dict(status='LIBRARY_SOURCE_ADMISSION_OPEN',runs={},sources={},llbc={},
    source_revision=plan['source_revision'],features=plan['features'],
    print_axioms='N/A: evidence collection only; no Lean result or source admission inferred')
for attempt in plan['attempts']:
    source=root/'runs'/attempt;target=out/'runs'/attempt
    target.mkdir(parents=True)
    receipt=json.loads((source/'receipt.json').read_text())
    assert receipt['process_swaps']==0
    assert receipt['cgroup_swap_current']=='0'
    files={}
    for name in ['receipt.json','stdout.log','stderr.log','time.log']:
        p=source/name
        if not p.exists():continue
        files[name]=dict(remote_path=str(p),sha256=sha(p),bytes=p.stat().st_size)
        if attempt=='cu-array-source-aeneas-b' and name=='stdout.log':
            data=p.read_bytes();anchor=b"Argument 0 doesn't have the proper type:"
            position=data.index(anchor)
            excerpt=data[max(0,position-2500):position+1800]
            (target/'stdout-error-excerpt.log').write_bytes(excerpt)
            files[name]['retention']='Full trace retained remotely; only exact byte excerpt copied.'
            files[name]['excerpt_start']=max(0,position-2500)
            files[name]['excerpt_end_exclusive']=min(len(data),position+1800)
        else:(target/name).write_bytes(p.read_bytes())
    manifest['runs'][attempt]=dict(exit_status=receipt['exit_status'],files=files)
standard=Path('/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src')
for name,source in [
    ('array-mod.rs',standard/'array/mod.rs'),
    ('try-trait.rs',standard/'ops/try_trait.rs'),
    ('backend-Core-Ops.lean',Path('/home/dombarker/project-offloads/aspis-r1-j17-port-20261015/backend/Aeneas/Std/Core/Ops.lean'))]:
    (out/name).write_bytes(source.read_bytes())
    manifest['sources'][name]=dict(path=str(source),sha256=sha(source),bytes=source.stat().st_size)
for name in ['CuDots.llbc','CuDotsArraySource.llbc','CuDotsArrayMono.llbc','CuDotsArrayElaborated.llbc']:
    p=root/name
    manifest['llbc'][name]=dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size)
manifest['rustc_version']=subprocess.check_output([
    '/home/dombarker/.cargo/bin/rustup','run','nightly-2026-06-01','rustc','-Vv'],text=True)
(out/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(dict(status=manifest['status'],runs=len(manifest['runs']),
    manifest_sha256=sha(out/'MANIFEST.json'),print_axioms='N/A: diagnostics only')))
