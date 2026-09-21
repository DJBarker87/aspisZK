#!/usr/bin/env python3
"""Run inside a bounded Linux build scope. Compilation only; never deploy."""
import json
import hashlib
import os
from pathlib import Path
import subprocess
import sys

root = Path(sys.argv[1]).resolve()
assert root.name.startswith('aspis-r17-sbf-probe-') and not (root / '.git').exists()
stage = json.loads((root / 'r17-sbf-probe.json').read_text())
callback = root / 'docs/research/v8-no-work-100-20260907/experiments/relation_callback.rs'
assert hashlib.sha256(callback.read_bytes()).hexdigest() == stage['callback_after_sha256']
host = json.loads((root / 'r17-stage.json').read_text())
def check_after(name, expected):
    if name in stage.get('owned_weights', {}):
        change = stage['owned_weights'][name]
        assert change['before_sha256'] == expected
        expected = change['after_sha256']
    if name in stage.get('lazy_reference', {}):
        change = stage['lazy_reference'][name]
        assert change['before_sha256'] == expected
        expected = change['after_sha256']
    if name in stage.get('move_prepared', {}):
        change = stage['move_prepared'][name]
        assert change['before_sha256'] == expected
        expected = change['after_sha256']
    if name in stage.get('fast_g_reuse', {}):
        change = stage['fast_g_reuse'][name]
        assert change['before_sha256'] == expected
        expected = change['after_sha256']
    if name in stage.get('fast_g_reuse_only', {}):
        change = stage['fast_g_reuse_only'][name]
        assert change['before_sha256'] == expected
        expected = change['after_sha256']
    if name in stage.get('fused_fft', {}):
        change = stage['fused_fft'][name]
        assert change['before_sha256'] == expected
        expected = change['after_sha256']
    if name in stage.get('scalar_fma', {}):
        change = stage['scalar_fma'][name]
        assert change['before_sha256'] == expected
        expected = change['after_sha256']
    if name in stage.get('inplace_fold_relation', {}):
        change = stage['inplace_fold_relation'][name]
        assert change['before_sha256'] == expected
        expected = change['after_sha256']
    assert hashlib.sha256((callback.parent / name).read_bytes()).hexdigest() == expected
if 'inplace_dense_fold' in stage:
    change = stage['inplace_dense_fold']
    assert change['before_sha256'] == '7e12acf033a9c309a836dcb1c334c69932e15b97407613b3968f8e1c53787ead'
    assert change['path'] == 'crates/aspis-core/src/sumcheck.rs'
    assert hashlib.sha256((root / change['path']).read_bytes()).hexdigest() == change['after_sha256']
if 'owned_weights' in stage:
    assert hashlib.sha256((callback.parent / 'r17_owned_weights.rs').read_bytes()).hexdigest() == stage['owned_weights_sha256']
if 'fixed_g_table' in stage:
    change = stage['fixed_g_table']
    assert change['before_sha256'] == stage['base_power_specialization']['after_sha256']
    expected = change['after_sha256']
    if 'fast_g' in stage:
        fast = stage['fast_g']
        assert fast['before_sha256'] == expected
        expected = fast['after_sha256']
        for name in ('r17_fast_g.rs', 'r17_fast_g_generate.rs'):
            check_after(name, fast[name])
        assert hashlib.sha256((callback.parent / 'r17_fast_g_tables.rs').read_bytes()).hexdigest() == fast['tables_sha256']
    assert expected == stage['workspace_sha256']
    assert hashlib.sha256((callback.parent / 'r17_g_powers.rs').read_bytes()).hexdigest() == change['table_sha256']
if 'workspace_adapter' in stage:
    for name, hashes in stage['workspace_adapter'].items():
        if name in stage.get('tensor_prefix', {}):
            assert stage['tensor_prefix'][name]['before_sha256'] == hashes['after_sha256']
            continue
        assert hashlib.sha256((callback.parent / name).read_bytes()).hexdigest() == hashes['after_sha256']
    assert hashlib.sha256((callback.parent / 'r17_mask_workspace.rs').read_bytes()).hexdigest() == stage['workspace_sha256']
if 'tensor_prefix' in stage:
    for name, hashes in stage['tensor_prefix'].items():
        check_after(name, hashes['after_sha256'])
    assert hashlib.sha256((callback.parent / 'r17_tensor_prefix.rs').read_bytes()).hexdigest() == stage['tensor_prefix_sha256']
if 'basis_specialization' in stage:
    basis = callback.parent / 'r16_basis_transport.rs'
    table = callback.parent / 'r17_basis_tables.rs'
    assert hashlib.sha256(basis.read_bytes()).hexdigest() == stage['basis_specialization']['after_sha256']
    assert hashlib.sha256(table.read_bytes()).hexdigest() == stage['basis_specialization']['table_sha256']
    gate_env = dict(os.environ)
    gate_env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',
        CARGO_TARGET_DIR='/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz/docs/research/v8-no-work-100-20260907/experiments/performance-host/target')
    for key in ('RUSTFLAGS', 'RUSTC'):
        gate_env.pop(key, None)
    actual = subprocess.check_output(['/home/dombarker/.cargo/bin/cargo', 'run',
        '--offline', '--locked', '--release', '--jobs', '2', '--manifest-path',
        str(callback.parent / 'performance-host/Cargo.toml'), '--bin', 'r17-export-basis'],
        env=gate_env, cwd=root)
    assert actual == table.read_bytes(), 'actual host constructor and SBF table differ'
    print('PASS: all 1024 permutation and inactive entries equal actual host constructor', flush=True)
for item in host['r17_edits'] + host['r17_shared']:
    path = root / item['path']
    if path == callback:
        continue
    if path.name in stage.get('tensor_prefix', {}):
        assert stage['tensor_prefix'][path.name]['before_sha256'] == item.get('after_sha256', item.get('sha256'))
        continue
    if path.name in stage.get('cu_profile', {}):
        change = stage['cu_profile'][path.name]
        assert change['before_sha256'] == item.get('after_sha256', item.get('sha256'))
        check_after(path.name, change['after_sha256'])
        continue
    if path.name in stage.get('workspace_adapter', {}):
        assert stage['workspace_adapter'][path.name]['before_sha256'] == item.get('after_sha256', item.get('sha256'))
        continue
    assert hashlib.sha256(path.read_bytes()).hexdigest() == item.get('after_sha256', item.get('sha256')), path
env = dict(os.environ)
env.update(NO_DNA='1',
    PATH='/home/dombarker/.cargo/bin:/home/dombarker/.local/share/solana/install/active_release/bin:/usr/bin:/bin',
    RUSTC='/home/dombarker/.cache/solana/v1.54/platform-tools/rust/bin/rustc',
    RUSTFLAGS=stage['rustflags'],
    CARGO_TARGET_DIR='/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz/docs/research/v8-no-work-100-20260907/experiments/performance-sbf/target')
process = subprocess.Popen([
    '/usr/bin/time', '-v',
    '/home/dombarker/.local/share/solana/install/active_release/bin/cargo-build-sbf',
    '--offline', '--skip-tools-install', '--no-rustup-override', '--tools-version', 'v1.54',
    '--jobs', '2', '--features', stage['features'],
    '--manifest-path', str(root / stage['manifest']),
    '--sbf-out-dir', str(root / 'sbf-output'),
], env=env, cwd=root, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
frame_error = False
for line in process.stdout:
    print(line, end='', flush=True)
    if ('overflows the maximum allowed frame' in line or
            ('Stack offset' in line and 'exceeded' in line)):
        frame_error = True
code = process.wait()
if frame_error:
    print('FAIL: SBF frame diagnostic; ELF is not accepted for measurement', flush=True)
raise SystemExit(code or int(frame_error))
