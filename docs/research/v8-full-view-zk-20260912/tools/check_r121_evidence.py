#!/usr/bin/env python3
"""Audit the new exact-field source gate, without claiming oracle security."""
import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from audit_r121_source import audit

parser = argparse.ArgumentParser()
parser.add_argument('--record', action='store_true')
args = parser.parse_args()
root = Path(__file__).resolve().parent.parent
repo = root.parents[2]
evidence = root / 'evidence/r121-two-swap-source'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text())


def blob(h):
    path = evidence / 'blobs' / h
    assert sha(path) == h
    return path


def metrics(path):
    s = path.read_text()
    duration = re.findall(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)', s)[-1]
    return {'exit': int(re.findall(r'Exit status: (\d+)', s)[-1]),
            'swaps': int(re.findall(r'Swaps: (\d+)', s)[-1]),
            'wall_s': round(sum(float(x)*60**i for i, x in enumerate(reversed(duration.split(':')))), 2),
            'peak_rss_kib': int(re.findall(r'Maximum resident set size \(kbytes\): (\d+)', s)[-1])}


subprocess.run([sys.executable, str(root / 'tools/check_r120_evidence.py')], check=True, stdout=subprocess.DEVNULL)
subprocess.run([sys.executable, str(root / 'tools/freeze_r121_manifest.py'), '--check'], check=True, stdout=subprocess.DEVNULL)
table = audit()
assert table == read(evidence / 'source-table-audit.json')
collection = read(evidence / 'collection.json')
assert collection['all_selected_native_source_pins_verified']
assert collection['selected_native_manifest_sha256'] == table['selected_native_manifest_sha256']
selected = read(root / 'evidence/r117-native-engine/r117-primal/r18-stage.json')
assert collection['selected_native_files_verified'] == len(selected['files'])
assert collection['resources'] == {'memory.high': str(2**30), 'memory.max': str(2*2**30), 'memory.swap.max': '0', 'pids.max': '128'}
assert not any(collection[k] for k in ['private_fixtures_collected', 'compiled_objects_collected', 'wallet_keys_collected', 'verifier_changed'])
plan = read(root / 'tools/r121-release-manifest.json')
assert len(plan['targets']) == 12
formal = read(evidence / 'formal.json')
assert len(formal) == 16
failures = {'table-a': 'TwoSwapSourceTable.log', 'table-b': 'TwoSwapSourceTable.log',
            'weights-a': 'TwoSwapSourceWeights.log', 'fixed-a': 'TwoSwapSourceFixed.log',
            'source-a': 'TwoSwapResidualSource.log', 'minor-a': 'TwoSwapSourceMinor.log',
            'minor-b': 'TwoSwapSourceMinor.log', 'minor-c': 'TwoSwapSourceMinor.log'}
reports = {}
release = None
preflight = {}
for name, record in formal.items():
    component, attempt = name.removeprefix('aspis-r121-').split('-20260930-')
    short = component + '-' + attempt
    artifacts = record['artifacts']
    for h in artifacts.values():
        blob(h)
    caps = read(blob(artifacts['resources.json']))
    assert [caps[k] for k in ['memory.high', 'memory.max', 'memory.swap.max', 'pids.max']] == [str(5*2**30), str(7*2**30), '0', '128']
    logs, audits = {}, {}
    for filename, h in artifacts.items():
        if not filename.endswith('.log'):
            continue
        path = blob(h)
        s = path.read_text()
        m = metrics(path)
        logs[filename] = m
        assert m['exit'] == (1 if failures.get(short) == filename else 0), (short, filename, m)
        assert m['swaps'] == 0 and m['peak_rss_kib'] < 7*2**20
        declarations = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", s, re.S)
        audits[filename] = {d: [x.strip() for x in axioms.split(',') if x.strip()] for d, axioms in declarations}
        if not m['exit']:
            assert 'sorryAx' not in s
            assert all(set(xs) <= {'propext', 'Classical.choice', 'Quot.sound'} for xs in audits[filename].values())
    records = read(blob(artifacts['metadata.json'])) if 'metadata.json' in artifacts else []
    current = [r for r in records if '/' + name + '/lib/' in ' '.join(r.get('command', []))]
    if short == 'table-a':
        assert 'no such file or directory' in blob(artifacts['TwoSwapSourceTable.log']).read_text()
        # The upload race ended before the source hash could be recorded.
        assert len(current) <= 1
    else:
        assert len(current) == len(logs)
    for r in current:
        filename = Path(r['target_name']).name + '.log'
        assert r['exit'] == logs[filename]['exit']
        assert r['base_revision'] == plan['base_revision'] and r['toolchain'] == plan['toolchain']
        assert r['command'][0].endswith('/lake') and r['command'][1:3] == ['env', 'lean']
        assert '-j1' in r['command'] and '-M4500' in r['command']
        if r['exit'] == 0 and short != 'release-a':
            preflight[r['target_name']] = r['source_sha256']
    reports[name] = {'targets': current, 'metrics': logs, 'axioms': audits}
    if short == 'release-a':
        assert [r['target_name'] for r in current] == [r['target'] for r in plan['targets']]
        for r, pin in zip(current, plan['targets'], strict=True):
            assert r['exit'] == 0 and r['source_sha256'] == pin['sha256']
            assert sha(root / 'lean' / (r['target_name'] + '.lean')) == pin['sha256']
            assert len(audits[Path(r['target_name']).name + '.log']) == pin['axioms_audits']
        deps = read(blob(artifacts['dependency-pins.json']))
        for path, h in deps.items():
            prefix = '/home/dombarker/project-offloads/aspis-r57-lean-src-20260929-a/'
            if path.startswith(prefix):
                assert sha(root / 'lean' / path.removeprefix(prefix)) == h
        release = reports[name]
assert release is not None
assert all(preflight[r['target']] == r['sha256'] for r in plan['targets'])
summary = {
    'status': 'PASS_SCOPED', 'base_revision': plan['base_revision'],
    'table_audit': table, 'formal': reports,
    'compiled_release_targets': len(plan['targets']),
    'release_axioms_audits': sum(r['axioms_audits'] for r in plan['targets']),
    'release_wall_sum_s': round(sum(r['wall_s'] for r in release['metrics'].values()), 2),
    'release_max_leaf_rss_kib': max(r['peak_rss_kib'] for r in release['metrics'].values()),
    'release_swaps': 0, 'retained_failed_preflights': len(failures),
    'arbitrary_challenge_exact_field_weight_binding': True,
    'two_swap_fixed_query_polynomial_nonzero': True,
    'determinant_total_degree_bound': 819,
    'actual_rational_chord_scale_bound': True,
    'adaptive_shared_oracle_probability_bound': False,
    'actual_source_universal_joint_coverage': False,
    'rust_word_refinement': False, 'full_privacy': False, 'full_soundness': False,
    'verifier_changed': False, 'new_SBF_runs': 0, 'unchanged_CU': [999790, 999532],
    'first_remaining_proposition': 'Justify the exceptional-event law for this new residual polynomial in the actual adaptive shared-oracle experiment, where query roots may depend on earlier challenges. Combine the result with universal joint C1/H1/G affine-image compatibility, not merely this G-residual minor.',
}
tools = ['audit_r121_source.py', 'freeze_r121_manifest.py', 'r121-release-manifest.json',
         'run_r121_lean.py', 'run_r121_release.py', 'collect_r121_evidence.py', 'check_r121_evidence.py']
paths = [root / 'tools' / n for n in tools] + [root / 'lean' / (r['target'] + '.lean') for r in plan['targets']]
paths += [root / 'evidence/r120-augmented-section/MANIFEST.json']
pins = {str(path.relative_to(repo)): sha(path) for path in sorted(paths)}
if args.record:
    (evidence / 'receipt.json').write_text(json.dumps(summary, indent=2, sort_keys=True) + '\n')
    (evidence / 'SOURCE_PINS.json').write_text(json.dumps(pins, indent=2) + '\n')
    (evidence / 'MANIFEST.json').write_text(json.dumps({str(p.relative_to(evidence)): sha(p)
        for p in sorted(evidence.rglob('*')) if p.is_file() and p.name != 'MANIFEST.json'}, indent=2) + '\n')
assert read(evidence / 'receipt.json') == summary and read(evidence / 'SOURCE_PINS.json') == pins
manifest = read(evidence / 'MANIFEST.json')
assert set(manifest) == {str(p.relative_to(evidence)) for p in evidence.rglob('*') if p.is_file() and p.name != 'MANIFEST.json'}
for name, h in manifest.items():
    assert sha(evidence / name) == h
print(json.dumps({k: summary[k] for k in ['status', 'compiled_release_targets', 'release_axioms_audits',
    'release_wall_sum_s', 'release_max_leaf_rss_kib', 'two_swap_fixed_query_polynomial_nonzero',
    'determinant_total_degree_bound', 'adaptive_shared_oracle_probability_bound', 'full_privacy', 'full_soundness']}))
