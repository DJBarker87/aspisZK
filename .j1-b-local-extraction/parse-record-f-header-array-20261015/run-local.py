#!/usr/bin/env python3
"""One pinned, dependency-free local source extraction with a group RSS guard.

macOS has no cgroup hard cap here. Sample whole process-group RSS every 50 ms
and kill at 3 GiB, leaving 0.5 GiB below the authorized 3.5 GiB ceiling.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import signal
import shutil
import subprocess
import threading
import time
import tomllib

CLI = argparse.ArgumentParser()
CLI.add_argument('--target', choices=['row-shape', 'parse-record'], required=True)
CLI.add_argument('--output', type=Path, required=True)
CLI.add_argument('--mir', choices=['built', 'optimized'], default='built')
CLI.add_argument('--include-option-methods', action='store_true')
ARGS = CLI.parse_args()
KIT_ROOT = Path(__file__).resolve().parent
ROOT = KIT_ROOT.parents[4]
KIT = KIT_ROOT / ARGS.target
OUT = ARGS.output.resolve()
TARGET_NAME = 'row_shape' if ARGS.target == 'row-shape' else 'parse_record'
NAMESPACE = 'AspisR1RowShape' if ARGS.target == 'row-shape' else 'AspisR1RecordParser'
CHARON_ROOT = Path('/Users/dominic/ZK/external/aeneas/charon-cb50-metadata')
AENEAS_ROOT = Path('/Users/dominic/ZK/external/aeneas/aeneas-verif-workspace/aeneas')
CHARON = CHARON_ROOT / 'bin/charon'
AENEAS = AENEAS_ROOT / 'bin/aeneas'
SYSROOT = Path('/Users/dominic/.rustup/toolchains/nightly-2026-06-01-aarch64-apple-darwin')
TOOL_PINS = {
    CHARON: '776344b8bfb7f3ec4ba78d5007ae79c1ef3f4ed654de05f04266693759a37375',
    CHARON_ROOT / 'bin/charon-driver': 'cc41d8ca83d7d0b9ae9ff8484e091d74ec91d90e9da0064f7731a0b355c1b806',
    AENEAS: 'fbb8dac1a9a57e635a762e04b95aeb46dbd2dab2be5ed54fa9e0b1321c1962cf',
}
LIMIT_KIB = 3_145_728
TIMEOUT = 180

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')

def git(*args, cwd=ROOT):
    return subprocess.check_output(['git', '-C', str(cwd), *args], text=True).strip()

def swap():
    return subprocess.check_output(['/usr/sbin/sysctl', 'vm.swapusage'], text=True).strip()

def main():
    assert not OUT.exists(), 'Use a fresh output directory; preserve earlier evidence.'
    for path, expected in TOOL_PINS.items():
        assert sha(path) == expected, f'tool pin mismatch: {path}'
    package = tomllib.loads((KIT / 'Cargo.toml').read_text())
    assert not any('dependencies' in key for key in package), 'Unexpected dependencies'
    assert 'target' not in package, 'Unexpected target dependency tables'
    pins = json.loads((KIT / 'source-pins.json').read_text())
    for name, entry in pins['sources'].items():
        assert sha(KIT / name) == entry['sha256'], f'input pin mismatch: {name}'
    check = subprocess.run(['python3', str(KIT_ROOT / 'extract.py'), '--check', '--target', ARGS.target],
                           cwd=ROOT, capture_output=True, text=True)
    assert check.returncode == 0, check.stdout + check.stderr
    OUT.mkdir(parents=True)
    source = OUT / 'source'
    source.mkdir()
    for name in sorted(set(pins['sources']) | {'source-pins.json'}):
        dest = source / name
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(KIT / name, dest)
    shutil.copy2(__file__, OUT / 'run-local.py')
    (OUT / 'source-check.log').write_text(check.stdout + check.stderr)
    env = dict(os.environ)
    for key in ['RUSTC', 'RUSTC_WRAPPER', 'RUSTC_WORKSPACE_WRAPPER', 'RUSTFLAGS',
                'CARGO_ENCODED_RUSTFLAGS', 'RUSTDOCFLAGS', 'CARGO_BUILD_TARGET']:
        env.pop(key, None)
    overrides = {
        'PATH': f'{SYSROOT}/bin:/Users/dominic/.cargo/bin:/usr/bin:/bin:/usr/sbin',
        'DYLD_LIBRARY_PATH': str(SYSROOT / 'lib'),
        'RUSTUP_TOOLCHAIN': 'nightly-2026-06-01',
        'CHARON_TOOLCHAIN_IS_IN_PATH': '1',
        'CARGO_BUILD_JOBS': '1',
        'CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS': 'true',
        'CARGO_TARGET_DIR': str(OUT / 'target'),
        'CARGO_NET_OFFLINE': 'true',
        'NO_DNA': '1',
    }
    env.update(overrides)
    write_json(OUT / 'environment.json', overrides)
    write_json(OUT / 'tool-pins.json', {str(p): s for p, s in TOOL_PINS.items()})
    write_json(OUT / 'provenance.json', {
        'worktree_revision': git('rev-parse', 'HEAD'),
        'worktree_status': git('status', '--short'),
        'charon_source_snapshot_revision': git('rev-parse', 'HEAD', cwd=CHARON_ROOT),
        'aeneas_source_snapshot_revision': git('rev-parse', 'HEAD', cwd=AENEAS_ROOT),
        'historical_charon_source': 'cb50ff16b9f1066b8a97dc06da704de2da2fa41c',
        'historical_aeneas_source': 'b59d5188c082f704a418c7cb4e52ad69328002d1',
        'binary_source_correspondence': 'Not independently rebuilt or proved; binary hashes and source snapshots recorded separately.',
        'guard': {'process_group_rss_kib': LIMIT_KIB, 'sample_seconds': 0.05,
                  'timeout_seconds_per_command': TIMEOUT, 'hard_cgroup_cap': False},
        'runner_sha256': sha(Path(__file__)),
    })
    write_json(OUT / 'input-pins.json', {str(p.relative_to(source)): sha(p)
                                       for p in source.rglob('*') if p.is_file()})
    records = []

    def run(label, command):
        cmd = [str(s) for s in command]
        before = swap()
        started = time.monotonic()
        stats = {'peak_group_rss_kib': 0, 'samples': 0, 'killed_reason': None}
        done = threading.Event()
        with (OUT / f'{label}.log').open('w') as log:
            proc = subprocess.Popen(cmd, cwd=source, env=env, stdout=log,
                                    stderr=subprocess.STDOUT, start_new_session=True)
            def monitor():
                while not done.is_set():
                    rows = subprocess.check_output(
                        ['/bin/ps', '-axo', 'pid=,pgid=,rss='], text=True).splitlines()
                    rss = sum(int(row.split()[2]) for row in rows
                              if len(row.split()) == 3 and int(row.split()[1]) == proc.pid)
                    stats['samples'] += 1
                    stats['peak_group_rss_kib'] = max(stats['peak_group_rss_kib'], rss)
                    reason = ('rss_guard' if rss >= LIMIT_KIB else
                              'timeout' if time.monotonic() - started > TIMEOUT else None)
                    if reason:
                        stats['killed_reason'] = reason
                        try:
                            os.killpg(proc.pid, signal.SIGKILL)
                        except ProcessLookupError:
                            pass
                        break
                    done.wait(0.05)
            worker = threading.Thread(target=monitor, daemon=True)
            worker.start()
            _, status, usage = os.wait4(proc.pid, 0)
            proc.returncode = os.waitstatus_to_exitcode(status)
            done.set()
            worker.join()
        record = {'label': label, 'command': cmd, 'exit': proc.returncode,
                  'wall_seconds': time.monotonic() - started, **stats,
                  'wait4_max_rss_bytes_macos': usage.ru_maxrss,
                  'wait4_swaps': usage.ru_nswap, 'swap_before': before, 'swap_after': swap()}
        records.append(record)
        write_json(OUT / 'commands.json', records)
        print(json.dumps(record), flush=True)
        if proc.returncode:
            print((OUT / f'{label}.log').read_text()[-6000:], flush=True)
            raise SystemExit(proc.returncode)

    run('charon-version', [CHARON, 'version'])
    run('aeneas-version', [AENEAS, '-version'])
    run('rustc-version', [SYSROOT / 'bin/rustc', '--version', '--verbose'])
    run('lock', [SYSROOT / 'bin/cargo', 'generate-lockfile', '--offline'])
    lock = tomllib.loads((source / 'Cargo.lock').read_text())
    assert len(lock['package']) == 1 and not lock['package'][0].get('dependencies')
    run('extract', [CHARON, 'cargo', '--preset', 'aeneas', '--mir', ARGS.mir,
                    '--sysroot', 'default', '--include',
                    'core::option' if ARGS.include_option_methods else 'core::option::Option',
                    '--include', 'core::result::Result', '--start-from',
                    'crate::r1_wire',
                    '--dest-file', OUT / 'RecordParser.llbc', '--',
                    '--locked', '--offline', '--release', '--lib',
                    '--no-default-features'])
    llbc = json.loads((OUT / 'RecordParser.llbc').read_text())
    (OUT / 'llbc-top-level-keys.json').write_text(json.dumps(list(llbc), indent=2) + '\n')
    assert llbc['has_errors'] is False, 'Charon reported translation errors'
    assert llbc['translated']['ordered_decls'], 'Empty ordered declarations: invalid root extraction'
    run('translate', [AENEAS, '-sequential', '-no-progress-bar', '-abort-on-error',
                      '-backend', 'lean', '-namespace', NAMESPACE,
                      '-dest', OUT / 'generated', '-subdir', NAMESPACE,
                      '-split-files', '-emit-json', OUT / 'RecordParser.llbc'])
    translation_path = OUT / 'generated/translation.json'
    assert translation_path.is_file(), 'No translation manifest'
    translation = json.loads(translation_path.read_text())
    found = [f for f in translation.get('functions', [])
             if f.get('is_local') and f.get('rust_name', '').endswith('::' + TARGET_NAME)]
    opaque = [f for f in translation.get('functions', []) if f.get('is_opaque')]
    write_json(OUT / 'translation-audit.json', {
        'target_name': TARGET_NAME, 'emitted_target': found, 'opaque_functions': opaque})
    assert len(found) == 1, 'Expected exactly one local target declaration'
    assert not opaque, 'Unresolved opaque function: inspect includes and retained standard-library bodies'
    decl = found[0]
    generated = OUT / 'generated' / decl['lean_file']
    assert generated.is_file() and decl['lean_name'].rsplit('.', 1)[-1] in generated.read_text()
    print('GENERATED: source only; no Lean compile or Rust/Lean refinement established.', flush=True)

if __name__ == '__main__':
    try:
        main()
    finally:
        if OUT.exists():
            write_json(OUT / 'artifact-pins.json', {
                str(p.relative_to(OUT)): sha(p) for p in OUT.rglob('*')
                if p.is_file() and 'target' not in p.relative_to(OUT).parts
                and p.name != 'artifact-pins.json'})
