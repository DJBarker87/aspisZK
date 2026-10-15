#!/usr/bin/env python3
"""Extract unchanged field parsers using the pinned NUC Charon/Aeneas pair.

Run only inside a capped, swap-disabled build-host scope. Expected time is
dependency-free release compilation, MIR extraction, and Lean translation.
The input directory contains this task's extraction kit and pinned full field
sources; no runtime source is edited here. Each output directory is immutable.
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


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--entry', default='crate::parse_fields_probe')
    parser.add_argument('--namespace', default='AspisR1FieldParser')
    parser.add_argument('--monomorphize', action='store_true')
    parser.add_argument('--mir', choices=['built', 'promoted', 'elaborated', 'optimized'],
                        default='built')
    args = parser.parse_args()
    for path, expected in TOOLS.items():
        assert sha(path) == expected, path
    pins = json.loads((args.input / 'source-pins.json').read_text())
    for relative, record in pins['sources'].items():
        assert sha(args.input / relative) == record['sha256'], relative
    assert not args.output.exists(), 'Use a new attempt directory; preserve previous attempts.'
    args.output.mkdir(parents=True)
    shutil.copy2(Path(__file__), args.output / 'extract-runner.py')
    source = args.output / 'source'
    source.mkdir()
    for relative in ['Cargo.toml', 'lib.rs', 'source-pins.json', *pins['sources']]:
        dest = source / relative
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(args.input / relative, dest)
    env = dict(os.environ, PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',
               RUSTUP_TOOLCHAIN='nightly-2026-06-01', CARGO_BUILD_JOBS='1',
               CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',
               CARGO_TARGET_DIR=str(args.output / 'target'), NO_DNA='1')
    write_json(args.output / 'environment.json', {key: env[key] for key in [
        'PATH', 'RUSTUP_TOOLCHAIN', 'CARGO_BUILD_JOBS',
        'CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS', 'CARGO_TARGET_DIR', 'NO_DNA']})
    write_json(args.output / 'tool-pins.json', {str(path): value for path, value in TOOLS.items()})
    write_json(args.output / 'input-pins.json', {str(path.relative_to(source)): sha(path)
               for path in source.rglob('*') if path.is_file()})
    records = []

    def run(label: str, command: list[object]) -> None:
        cmd = [str(value) for value in command]
        with (args.output / (label + '.log')).open('w') as log:
            result = subprocess.run(['/usr/bin/time', '-v', '-o',
                                     str(args.output / (label + '.time.log')), *cmd],
                                    cwd=source, env=env, stdout=log, stderr=subprocess.STDOUT)
        records.append({'label': label, 'command': cmd, 'exit': result.returncode})
        write_json(args.output / 'commands.json', records)
        print(json.dumps(records[-1]), flush=True)
        if result.returncode:
            print((args.output / (label + '.log')).read_text()[-8000:], flush=True)
            raise SystemExit(result.returncode)

    run('rustc-version', ['rustc', '--version', '--verbose'])
    run('lock', ['cargo', 'generate-lockfile', '--offline'])
    run('extract', [CHARON, 'cargo', '--preset', 'aeneas', '--mir', args.mir, '--sysroot', 'default',
                    *(['--monomorphize'] if args.monomorphize else []),
                    '--include', 'core::option', '--include', 'core::result',
                    '--start-from', args.entry, '--dest-file',
                    args.output / 'R1FieldParser.llbc', '--', '--locked', '--offline',
                    '--release', '--lib', '--no-default-features'])
    run('translate', [AENEAS, '-sequential', '-no-progress-bar', '-abort-on-error',
                      '-backend', 'lean', '-namespace', args.namespace, '-dest',
                      args.output / 'generated', '-subdir', args.namespace,
                      '-split-files', '-emit-json', args.output / 'R1FieldParser.llbc'])
    artifacts = {str(path.relative_to(args.output)): sha(path)
                 for directory in [source, args.output / 'generated']
                 for path in directory.rglob('*') if path.is_file()}
    artifacts['R1FieldParser.llbc'] = sha(args.output / 'R1FieldParser.llbc')
    write_json(args.output / 'artifact-pins.json', artifacts)
    print(json.dumps({'status': 'TRANSLATED', 'pinned_artifacts': len(artifacts),
                      'scope': 'Generated source only; not yet Lean-checked or refined.'}), flush=True)


if __name__ == '__main__':
    main()
