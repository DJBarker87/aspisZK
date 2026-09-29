#!/usr/bin/env python3
"""Bounded source-library extraction experiment, not a source-proof gate.
Expected work: small release Rust/MIR extraction and Aeneas translation.
Keep the exact R67 eta normalization explicit; leave production bytes alone.
"""
import argparse
import hashlib
import json
import os
import shutil
import subprocess
from pathlib import Path

p = argparse.ArgumentParser()
p.add_argument('--output', type=Path, required=True)
p.add_argument('--case', choices=['chain', 'array'], required=True)
p.add_argument('--lift-try', action='store_true')
p.add_argument('--include-maybe-dangling', action='store_true')
a = p.parse_args()
root = Path('/home/dombarker/project-offloads')
stage = root / 'aspis-r20-r62-gather-20260929-b'
kit = Path(__file__).parent / 'r67-circle-extraction'
charon = root / 'ZK-v5-formal/toolchains/charon/bin/charon'
aeneas = root / 'aspis-v7-aeneas-source-unblock-20260830/aeneas-repro-r1'
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

assert sha(charon) == 'b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c'
assert sha(aeneas) == 'e3e6e658ad26168421eb37627561930c1e13afa978f77b214a1201d9c4faa813'
cg = Path('/sys/fs/cgroup') / Path('/proc/self/cgroup').read_text().strip().split('::', 1)[1].lstrip('/')
resources = {n: (cg/n).read_text().strip() for n in ['memory.high', 'memory.max', 'memory.swap.max', 'pids.max']}
assert resources == {'memory.high': str(5*2**30), 'memory.max': str(7*2**30), 'memory.swap.max': '0', 'pids.max': '128'}
manifest = json.loads((stage / 'r18-stage.json').read_text())
for name, digest in manifest['files'].items():
    assert sha(stage/name) == digest, name
assert not a.output.exists()
a.output.mkdir()
source = a.output/'source'
source.mkdir()
(a.output/'resources.json').write_text(json.dumps(resources, indent=2)+'\n')
for name in ['Cargo.toml', 'lib.rs']:
    shutil.copy2(kit/name, source/name)
for name in ['field.rs', 'circle.rs', 'r23_width.rs', 'r24_guarded_qm.rs', 'r25_checked_dot.rs']:
    shutil.copy2(stage/'crates/aspis-core/src'/name, source/name)
before = (source/'r24_guarded_qm.rs').read_text()
assert before.count('.map(u64::from)') == 2
(a.output/'original').mkdir()
shutil.copy2(source/'r24_guarded_qm.rs', a.output/'original/r24_guarded_qm.rs')
(source/'r24_guarded_qm.rs').write_text(before.replace('.map(u64::from)', '.map(|value| u64::from(value))'))
(a.output/'normalization.json').write_text(json.dumps({
    'before_sha256': sha(a.output/'original/r24_guarded_qm.rs'),
    'after_sha256': sha(source/'r24_guarded_qm.rs'), 'sites': 2,
    'source_normalization_verified': False, 'production_changed': False}, indent=2)+'\n')
env = dict(os.environ, PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',
           RUSTUP_TOOLCHAIN='nightly-2026-06-01', CARGO_BUILD_JOBS='1',
           CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true', CARGO_TARGET_DIR=str(a.output/'target'), NO_DNA='1')
(a.output/'environment.json').write_text(json.dumps({k: env[k] for k in [
    'RUSTUP_TOOLCHAIN', 'CARGO_BUILD_JOBS', 'CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS', 'CARGO_TARGET_DIR']}, indent=2)+'\n')
records = []
def run(label, command):
    command = list(map(str, command))
    with (a.output/(label+'.log')).open('w') as log:
        result = subprocess.run(['/usr/bin/time', '-v', *command], cwd=source, env=env, stdout=log, stderr=subprocess.STDOUT)
    records.append({'label': label, 'command': command, 'exit': result.returncode})
    (a.output/'commands.json').write_text(json.dumps(records, indent=2)+'\n')
    print((a.output/(label+'.log')).read_text(), flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)
includes = (['core::iter::adapters::chain', 'core::iter::traits::iterator::Iterator::any']
            if a.case == 'chain' else ['core::array'])
if a.include_maybe_dangling:
    includes.append('core::mem::maybe_dangling')
options = ['--lift-associated-types', 'core::ops::try_trait::Try'] if a.lift_try else []
run('lock', ['cargo', 'generate-lockfile', '--offline'])
run('extract', [charon, 'cargo', '--preset', 'aeneas', '--mir', 'built', '--sysroot', 'default',
    '--start-from', 'crate::circle_probe', *options, *[v for n in includes for v in ['--include', n]],
    '--dest-file', a.output/'R69Circle.llbc', '--', '--locked', '--offline', '--release', '--lib', '--no-default-features'])
run('translate', [aeneas, '-sequential', '-no-progress-bar', '-abort-on-error', '-backend', 'lean',
    '-namespace', 'AspisR69Circle', '-dest', a.output/'generated', '-subdir', 'AspisR69Circle',
    '-split-files', '-emit-json', a.output/'R69Circle.llbc'])
