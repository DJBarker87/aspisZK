#!/usr/bin/env python3
"""Run in a bounded Linux scope. Measures a helper relation, NOT full Aspis."""
import argparse, hashlib, json, os, shutil, subprocess
from pathlib import Path

p = argparse.ArgumentParser()
p.add_argument('--project', type=Path, required=True)
p.add_argument('--elf', type=Path)
p.add_argument('--wire', type=Path)
p.add_argument('--mode', choices=['helper', 'native'])
p.add_argument('--output', type=Path)
a = p.parse_args()
cache = Path('/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz/docs/research/v8-no-work-100-20260907/experiments/performance-svm/target')
binary = a.project / 'r21-svm-probe'
env = dict(os.environ, NO_DNA='1', PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin', CARGO_TARGET_DIR=str(cache))
if not binary.exists():
    assert not a.project.exists(), 'fresh project required'
    (a.project / 'src').mkdir(parents=True)
    baseline = Path('/home/dombarker/project-offloads/aspis-r20-svm-20260922-a')
    for name in ['Cargo.toml', 'Cargo.lock']:
        shutil.copy2(baseline / name, a.project / name)
    shutil.copy2(Path(__file__).with_name('r21_svm_probe.rs'), a.project / 'src/main.rs')
    cmd = ['/usr/bin/time', '-v', '/home/dombarker/.cargo/bin/cargo', 'build', '--release', '--offline', '--locked', '--jobs', '2', '--manifest-path', str(a.project / 'Cargo.toml')]
    with (a.project / 'compile.log').open('w') as f:
        subprocess.run(cmd, cwd=a.project, env=env, stdout=f, stderr=subprocess.STDOUT, check=True)
    shutil.copy2(cache / 'release/aspis-r17-svm-probe', binary)
if a.elf:
    assert a.wire and a.mode and a.output and not a.output.exists()
    a.output.mkdir()
    cmd = ['/usr/bin/time', '-v', str(binary), str(a.elf), str(a.wire), a.mode]
    with (a.output / 'svm.jsonl').open('w') as out, (a.output / 'time.txt').open('w') as err:
        subprocess.run(cmd, cwd=a.project, env=env, stdout=out, stderr=err, check=True)
    def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
    metadata = {'elf': str(a.elf), 'elf_sha256': sha(a.elf), 'wire': str(a.wire), 'wire_sha256': sha(a.wire), 'driver_sha256': sha(binary), 'driver_source_sha256': sha(a.project / 'src/main.rs'), 'cargo_lock_sha256': sha(a.project / 'Cargo.lock'), 'mode': a.mode, 'scope': 'ordinary+image ONLY', 'complete_aspis_verifier': False, 'command': cmd}
    (a.output / 'metadata.json').write_text(json.dumps(metadata, indent=2) + '\n')
    results = [json.loads(line) for line in (a.output / 'svm.jsonl').read_text().splitlines()]
    for row in results:
        if row['case'] == 'honest': print(json.dumps(row), flush=True)
    assert all(not row['accepted'] for row in results if row['case'] != 'honest'), 'mutation accepted'
