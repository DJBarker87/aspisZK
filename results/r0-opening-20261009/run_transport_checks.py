#!/usr/bin/env python3
"""Run R-G's remaining focused checks on Linux, each in a capped scope.

The core r0:: suite is recorded separately in rg-core.json; do not repeat an
unchanged regression. Set CARGO_TARGET_DIR to the existing pinned cache.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

here = Path(__file__).resolve().parent
root = here.parent.parent
os.chdir(root)
manifest = json.loads((here / 'rg-source-manifest.json').read_text())
for name, digest in manifest['sha256'].items():
    assert hashlib.sha256((root / name).read_bytes()).hexdigest() == digest, name
(here / 'rg-source-audit.json').write_text(json.dumps({
    'source_revision': manifest['source_revision'],
    'matched_files': len(manifest['sha256']), 'all_matched': True,
}, indent=2) + '\n')
env = dict(os.environ, CARGO_BUILD_JOBS='2', R0_EVIDENCE_DIR=str(here / 'transport'))
env['PATH'] = str(Path.home() / '.cargo/bin') + os.pathsep + env.get('PATH', '')
(here / 'transport').mkdir(exist_ok=True)
cargo = ['--release', '--config', 'profile.release.overflow-checks=true', '--locked', '--offline']
checks = [
    ('inventory-check', ['cargo', 'run', *cargo, '-p', 'aspis-statement', '--example', 'r0_transport_inventory', '--', '--check']),
    ('inventory-test', ['cargo', 'test', *cargo, '-p', 'aspis-statement', '--test', 'r0_transport', '--', '--nocapture']),
    ('kat-check', ['python3', 'results/r0-opening-20261009/generate_kats.py', '--check']),
    ('full-size', ['cargo', 'test', *cargo, '-p', 'aspis-core', '--lib', 'r0::opening_tests::full_size_roundtrip_corruption_and_domain_identity', '--', '--ignored', '--exact', '--nocapture', '--test-threads=1']),
    ('no-std', ['cargo', 'check', *cargo, '-p', 'aspis-core', '--lib', '--no-default-features']),
]
for name, command in checks:
    scopes = subprocess.check_output(['systemctl', '--user', 'list-units', '--type=scope', '--state=running', '--output=json'], text=True)
    (here / f'rg-{name}-reservations.json').write_text(scopes)
    # Expected heavy work: first compilation, then full-domain natural-basis
    # encoding and Merkle hashing. The honest quotient system is sparse.
    with (here / f'rg-{name}.log').open('w') as log:
        status = subprocess.run([
            'systemd-run', '--user', '--scope', '--quiet', f'--unit=aspis-r0-rg-{name}',
            '-p', 'MemoryHigh=4G', '-p', 'MemoryMax=6G', '-p', 'MemorySwapMax=0',
            'python3', str(here / 'record_run.py'), str(here / f'rg-{name}.json'),
            manifest['source_revision'], *command,
        ], env=env, stdout=log, stderr=subprocess.STDOUT).returncode
    print(f'{name}: exit {status}', flush=True)
    if status:
        print((here / f'rg-{name}.log').read_text()[-5000:])
        sys.exit(status)
