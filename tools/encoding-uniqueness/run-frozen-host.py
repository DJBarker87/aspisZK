#!/usr/bin/env python3
"""Run in the private task host directory after uploading the tracked source kit.
Use the previously identity-checked frozen sources for all 259 pinned inputs;
keep task-base sources as snapshots. Never writes to the reference workspace.
"""
from pathlib import Path
import hashlib,json,os,subprocess
H=Path('/home/dombarker/project-offloads/codex-cx-encoding-inj-20261021')
F=Path('/home/dombarker/project-offloads/codex-cx-asq8-kani-20261021/src')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
comparison=json.loads((H/'frozen-source-comparison.json').read_text())
rows=[]
for row in comparison['inputs']:
    name=row['path']; src=H/'src'/name
    expected=row['frozen_source_sha256']
    assert sha(F/name)==expected,name
    if not src.exists():
        src.parent.mkdir(parents=True,exist_ok=True)
        src.write_bytes((F/name).read_bytes())
    if sha(src)!=expected:
        snapshot=H/'task-base-snapshot'/name
        snapshot.parent.mkdir(parents=True,exist_ok=True)
        assert not snapshot.exists()
        snapshot.write_bytes(src.read_bytes())
        src.write_bytes((F/name).read_bytes())
    assert sha(src)==expected
    rows.append(dict(path=name,sha256=expected))
(H/'frozen-run-inputs.json').write_text(json.dumps(dict(
    task_revision=(H/'source-revision.txt').read_text().strip(),
    reference_revision='02a646121c59587352913bc19708bde25bba33fb',
    inputs=rows, test_sha256=sha(H/'src/tools/encoding-uniqueness/src/lib.rs'),
    cargo_lock_sha256=sha(H/'src/tools/encoding-uniqueness/Cargo.lock'),
    note='Four inherited research-only differences replaced in private host copy; shipped decoders identical before overlay.'),indent=2)+'\n')
subprocess.run(['python3',str(H/'harness/reservation.py'),str(H/'reservation-frozen-native.json')],check=True)
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',
    CARGO_BUILD_JOBS='4',CARGO_TARGET_DIR=str(H/'native-target'),
    RUSTFLAGS='-C link-arg=-Wl,--threads=4')
subprocess.run(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G',
    '-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'harness/capped.py'),
    str(H/'receipts/frozen-native'),
    'Optimized incremental compilation after frozen-source overlay, seven decoder tests and saved-proof tx1/tx2; no proof generation',
    '--','cargo','test','--manifest-path',str(H/'src/tools/encoding-uniqueness/Cargo.toml'),
    '--release','--offline','--locked','-j','4','--','--nocapture'],env=env,check=True,cwd=H)
