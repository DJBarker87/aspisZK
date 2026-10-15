#!/usr/bin/env python3
"""Pinned Charon/Aeneas runner for the exact public_bytes extraction input.

Preparation only: this runner has not been launched. Invoke only in a dedicated
swap-disabled cgroup after root review.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess

CHARON = Path('/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/bin/charon')
AENEAS = Path('/home/dombarker/project-offloads/aspis-v7-aeneas-source-unblock-20260830/aeneas-repro-r1')
TOOLS = {
    CHARON: 'b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c',
    AENEAS: 'e3e6e658ad26168421eb37627561930c1e13afa978f77b214a1201d9c4faa813',
}
DEFAULT_ENTRY = 'crate::pool_v1::pair_forest_semantic_terminal::r0::Public::public_bytes'


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--entry', default=DEFAULT_ENTRY)
    parser.add_argument('--namespace', default='AspisR1PublicSerializer')
    parser.add_argument('--mir', choices=['built', 'promoted', 'elaborated', 'optimized'], default='built')
    parser.add_argument('--monomorphize', action='store_true')
    args = parser.parse_args()

    for path, expected in TOOLS.items():
        if not path.is_file() or sha(path) != expected:
            raise SystemExit(f'tool pin mismatch: {path}')
    pin_file = args.input / 'source-pins.json'
    pins = json.loads(pin_file.read_text())
    for relative, record in pins['sources'].items():
        candidate = args.input / relative
        if not candidate.is_file() or sha(candidate) != record['sha256']:
            raise SystemExit(f'input source pin mismatch: {relative}')
    manifest = json.loads((args.input / 'source-manifest.json').read_text())
    for item in manifest['items']:
        fragment = args.input / item['fragment_path']
        if sha(fragment) != item['fragment_sha256']:
            raise SystemExit(f'origin fragment pin mismatch: {item["name"]}')
    if args.output.exists():
        raise SystemExit('Use a fresh output directory per attempt; existing artifacts are immutable.')
    args.output.mkdir(parents=True)
    shutil.copy2(Path(__file__), args.output / 'run-public-serializer-extraction.py')
    source = args.output / 'source'
    source.mkdir()
    for relative in ['Cargo.toml', 'lib.rs', 'source-manifest.json', 'source-pins.json', *pins['sources']]:
        origin = args.input / relative
        if not origin.is_file():
            raise SystemExit(f'missing pinned input file: {relative}')
        dest = source / relative
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(origin, dest)

    env = dict(os.environ, PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',
               RUSTUP_TOOLCHAIN='nightly-2026-06-01', CARGO_BUILD_JOBS='1',
               CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',
               CARGO_TARGET_DIR=str(args.output / 'target'), NO_DNA='1')
    write_json(args.output / 'environment.json', {key: env[key] for key in [
        'PATH', 'RUSTUP_TOOLCHAIN', 'CARGO_BUILD_JOBS',
        'CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS', 'CARGO_TARGET_DIR', 'NO_DNA']})
    write_json(args.output / 'tool-pins.json', {str(path): value for path, value in TOOLS.items()})
    write_json(args.output / 'runner-pin.json', {
        'path': str(Path(__file__).resolve()), 'sha256': sha(Path(__file__).resolve())})
    write_json(args.output / 'input-pins.json', {str(path.relative_to(source)): sha(path)
               for path in source.rglob('*') if path.is_file()})
    records = []

    def run(label: str, command: list[object]) -> None:
        cmd = [str(value) for value in command]
        time_file = args.output / f'{label}.time.log'
        log_file = args.output / f'{label}.log'
        with log_file.open('w') as log:
            result = subprocess.run(['/usr/bin/time', '-v', '-o', str(time_file), *cmd],
                                    cwd=source, env=env, stdout=log, stderr=subprocess.STDOUT)
        records.append({'label': label, 'command': cmd, 'exit': result.returncode})
        write_json(args.output / 'commands.json', records)
        print(json.dumps(records[-1]), flush=True)
        if result.returncode:
            print(log_file.read_text()[-8000:], flush=True)
            raise SystemExit(result.returncode)

    run('rustc-version', ['rustc', '--version', '--verbose'])
    run('lock', ['cargo', 'generate-lockfile', '--offline'])
    run('extract', [CHARON, 'cargo', '--preset', 'aeneas', '--mir', args.mir,
                    '--sysroot', 'default', *(['--monomorphize'] if args.monomorphize else []),
                    '--include', 'core::option', '--include', 'core::result',
                    '--start-from', args.entry, '--dest-file', args.output / 'PublicSerializer.llbc',
                    '--', '--locked', '--offline', '--release', '--lib',
                    '--no-default-features', '--features', 'r0'])
    run('translate', [AENEAS, '-sequential', '-no-progress-bar', '-abort-on-error',
                      '-backend', 'lean', '-namespace', args.namespace,
                      '-dest', args.output / 'generated', '-subdir', args.namespace,
                      '-split-files', '-emit-json', args.output / 'PublicSerializer.llbc'])
    artifacts = {str(path.relative_to(args.output)): sha(path)
                 for directory in [source, args.output / 'generated']
                 for path in directory.rglob('*') if path.is_file()}
    artifacts['PublicSerializer.llbc'] = sha(args.output / 'PublicSerializer.llbc')
    artifacts['run-public-serializer-extraction.py'] = sha(args.output / 'run-public-serializer-extraction.py')
    write_json(args.output / 'artifact-pins.json', artifacts)
    print(json.dumps({'status': 'TRANSLATED', 'pinned_artifacts': len(artifacts),
                      'scope': 'Generated source only; no Lean check or Rust/Lean refinement.'}), flush=True)
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
