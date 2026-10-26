#!/usr/bin/env python3
"""Read-only proof/evidence audit. This never launches a build or prover."""
from pathlib import Path
import hashlib, json, re, subprocess

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
freeze = json.loads((HERE / 'CPP_FREEZE.json').read_text())
for name, expected in freeze['files'].items():
    assert sha(ROOT / name) == expected, name
inputs = json.loads((HERE / 'CPP_RUST_INPUTS.json').read_text())
for row in inputs['inputs']:
    assert sha(ROOT / row['path']) == row['sha256'], row['path']
expected_limits = {'memory.high': '6442450944', 'memory.max': '8589934592',
                   'memory.swap.max': '0', 'pids.max': '64'}
receipts = []
for prefix, count in [('CPP_L', 100), ('CPP_K', 6), ('CPP_RUST', 1)]:
    for number in range(1, count + 1):
        name = f'{prefix}{number:03}'
        directory = HERE / name
        receipt = json.loads((directory / 'receipt.json').read_text())
        assert receipt['attempt'] == name
        assert receipt['limits'] == expected_limits, name
        assert receipt['swaps'] == '0', name
        for source, expected in receipt['source_hashes'].items():
            assert sha(directory / 'sources' / source) == expected, (name, source)
        assert all(k in receipt for k in ['command', 'source_revision', 'exit_status',
                                          'wall_seconds', 'peak_rss_kib', 'deps_fingerprint'])
        if prefix == 'CPP_L':
            assert '-M7000' in receipt['command'], name
            if receipt['exit_status'] == 0:
                assert not any('sorryAx' in line for line in receipt['print_axioms']), name
                for line in receipt['print_axioms']:
                    match = re.search(r'depends on axioms: \[([^]]*)\]', line)
                    if match:
                        assert set(filter(None, match[1].split(', '))) <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, line)
        else:
            assert '--release' in receipt['command'] or receipt['env'].get('CARGO_PROFILE_DEV_OPT_LEVEL') == '3', name
        receipts.append(receipt)
lean = [r for r in receipts if r['kind'] == 'lean']
assert len(lean) == 100
host = json.loads((HERE / 'CPP_HOST_OBJECTS.json').read_text())
assert host['native_157_inputs_match']
modules = sorted((ROOT / 'lean').glob('CPP_*.lean'))
verified = []
for module in modules:
    digest = sha(module)
    candidates = [r for r in lean if r['exit_status'] == 0 and r['source_hashes'].get(module.name) == digest]
    assert candidates, module.name
    assert host['objects'][module.stem][module.name]['sha256'] == digest, module.name
    assert module.with_suffix('.olean').name in host['objects'][module.stem], module.name
    body = module.read_text()
    assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s', body, re.M), module.name
    assert 'maxHeartbeats' not in body and 'maxRecDepth' not in body, module.name
    verified.append({'module': str(module.relative_to(ROOT)), 'sha256': digest,
                     'passing_attempt': candidates[-1]['attempt']})
final = next(r for r in lean if r['attempt'] == 'CPP_L100')
assert final['exit_status'] == 0
expected_names = set(json.loads((HERE / 'CPP_AXIOMS_TARGETS.json').read_text())) | {'AspisR1.T2R_Top.deployed'}
actual_names = set(re.match(r"'([^']+)'", line)[1] for line in final['print_axioms'])
assert actual_names == expected_names
changed = subprocess.check_output(['git', 'diff', '--name-only', freeze['revision']], cwd=ROOT, text=True).splitlines()
untracked = subprocess.check_output(['git', 'ls-files', '--others', '--exclude-standard'], cwd=ROOT, text=True).splitlines()
assert all(x.startswith('lean/CPP_') or x.startswith('evidence/cp-protect-20261026/') for x in changed + untracked)
for path in HERE.rglob('*'):
    if path.is_file():
        assert path.suffix not in {'.olean', '.ir', '.so', '.o', '.a', '.bin', '.elf', '.gz', '.tar', '.zip'}, path
for block in json.loads((HERE / 'CPP_guard' / 'CPP_SOURCE_MAP.json').read_text())['verbatim_blocks']:
    source = (ROOT / 'programs/r1-cost-probe/src/r1_pool_adapter_owned.rs').read_text()
    start = source.index(block['start'])
    brace = source.index('{', start)
    depth, end = 1, brace + 1
    while depth:
        depth += (source[end] == '{') - (source[end] == '}')
        end += 1
    text = source[start:end]
    assert hashlib.sha256(text.encode()).hexdigest() == block['sha256']
    assert text in (HERE / 'CPP_guard' / 'CPP_lib.rs').read_text()
summary = {'lean_attempts': len(lean), 'lean_pass': sum(r['exit_status'] == 0 for r in lean),
           'lean_diagnostic_fail': sum(r['exit_status'] != 0 for r in lean),
           'kani_submissions': 6, 'kani_pass': sum(r['kind'] == 'kani' and r['exit_status'] == 0 for r in receipts),
           'rust_tests': 1, 'current_modules': len(verified), 'final_axiom_targets': len(expected_names),
           'lean_wall_seconds_sum': sum(r['wall_seconds'] for r in lean),
           'lean_peak_rss_kib_max': max(int(r['peak_rss_kib']) for r in lean),
           'all_swaps_zero': True, 'global_ledger_rows_removed': 0,
           'verified_modules': verified}
(HERE / 'CPP_VALIDATION.json').write_text(json.dumps(summary, indent=2) + '\n')
(HERE / 'CPP_RUNS.json').write_text(json.dumps(receipts, indent=2) + '\n')
print(json.dumps({k: v for k, v in summary.items() if k != 'verified_modules'}, indent=2))
