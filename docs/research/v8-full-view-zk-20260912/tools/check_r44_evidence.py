#!/usr/bin/env python3
"""Audit the fixed-query section without promoting it to full source privacy.

--record freezes newly collected logs and current source pins. Normal operation
only verifies them; it does not rebuild unchanged Lean or runtime targets.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path

p = argparse.ArgumentParser()
p.add_argument('--record', action='store_true')
a = p.parse_args()
root = Path(__file__).resolve().parent.parent
repo = root.parents[2]
e = root / 'evidence/r44-normalized-query-section'
base = '29ad29d3bfbf1bf0e0e527f4a2c1afd40f6aed48'
checks = [
    ('c', 'NormalizedQuerySection', 8),
    ('m', 'NormalizedQuotient', 9),
    ('d', 'HighWitnessFieldTransport', 4),
    ('m', 'QM31NormalizedSection', 6),
    ('h', 'HighQueryGCore', 8),
    ('m', 'NormalizedGCore', 4),
    ('m', 'NormalizedSectionBoundary', 4),
    ('m', 'NormalizedSectionAudit', 10),
]
prereqs = [
    ('CircleNaturalBasisEval', 0), ('NaturalBasisCore', 0),
    ('FibreInterpolation', 2), ('NaturalCoverage', 2),
    ('FinalConsistency', 2), ('RawFinalKernel', 3),
]

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def metrics(path, audits):
    log = path.read_text()
    assert '\tExit status: 0' in log and '\tSwaps: 0' in log, path
    assert 'sorryAx' not in log
    axioms = re.findall(r'depends on axioms: \[([^]]*)\]', log)
    assert len(axioms) == audits, (path, len(axioms), audits)
    for ax in axioms:
        assert set(ax.replace('\n', '').replace(' ', '').split(',')) <= {
            'propext', 'Classical.choice', 'Quot.sound'}
    rss = int(re.search(r'Maximum resident set size \(kbytes\): (\d+)', log).group(1))
    t = re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)', log).group(1).split(':')
    return {'wall_seconds': round(sum(float(v)*60**i for i, v in enumerate(reversed(t))), 2),
            'peak_rss_kib': rss, 'swaps': 0, 'exit': 0}

records = json.loads((e / 'lean-m/metadata.json').read_text())
assert len(records) == 211
for r in records:
    assert r['exit'] == 0 and r['toolchain'] == 'leanprover/lean4:v4.32.0'
    assert sha(root / 'lean' / (r['target_name']+'.lean')) == r['source_sha256']

results = {}
for letter, name, audits in checks:
    results[name] = metrics(e / f'lean-{letter}/{name}.log', audits)
    source = root / f'lean/AspisV8R19/{name}.lean'
    src = source.read_text()
    assert len(re.findall(r'^theorem ', src, re.M)) == (0 if name.endswith('Audit') else audits)
    for bad in ('sorry', 'axiom ', 'native_decide', 'maxRecDepth', 'maxHeartbeats', 'norm_num'):
        assert bad not in src, (name, bad)
    record = next(r for r in records if r['target_name'] == f'AspisV8R19/{name}')
    assert record['base_revision'] == base
    assert f'/aspis-r44-lean-20260929-{letter}/lib/' in record['command'][6]
for name, audits in prereqs:
    results[name] = metrics(e / f'lean-a/{name}.log', audits)

assert sha(root / 'lean/AspisFormal/CircleNaturalBasisEval.lean') == sha(
    repo / 'AspisFormal/AspisFormal/CircleNaturalBasisEval.lean')
assert 'maximum recursion depth' in (e / 'lean-c/HighWitnessFieldTransport.log').read_text()
for letter in 'jkl':
    log = (e / f'lean-{letter}/NormalizedSectionBoundary.log').read_text()
    assert 'maximum number of heartbeats' in log and '\tExit status: 1' in log
new_names = [n for _, n, _ in checks if not n.endswith('Audit')]
receipt = {
    'base_revision': base,
    'new_theorems': 43,
    'retained_theorem_audits': 19,
    'final_cache_objects': 211,
    'resources': {'MemoryHigh': '3G', 'MemoryMax': '5G', 'MemorySwapMax': 0, 'TasksMax': 128,
                  'host_ram_gib': 62, 'host_available_gib_before': 44,
                  'max_simultaneous_reservation_gib': 5},
    'targets': results,
    'new_leaf_wall_seconds': round(sum(results[n]['wall_seconds'] for n in new_names), 2),
    'all_selected_wall_seconds': round(sum(r['wall_seconds'] for r in results.values()), 2),
    'peak_rss_kib': max(r['peak_rss_kib'] for r in results.values()),
    'all_distinct_QM31_root_tuples_at_fixed_specialization': True,
    'source_shaped_raw_final_G_core': True,
    'actual_Rust_normalization_refinement': False,
    'legal_mask_OOD_image_bridge_complete': False,
    'new_challenge_polynomial_and_degree': False,
    'source_shared_oracle_law': False,
    'full_privacy': False,
    'verifier_changed': False,
    'new_rust_execution': False,
    'new_sbf_measurement': False,
}
pins = {str((root / 'lean' / (r['target_name']+'.lean')).relative_to(repo)): r['source_sha256']
        for r in records}
for path in [root / 'tools/run_r44_lean.py', repo / 'AspisFormal/AspisFormal/CircleNaturalBasisEval.lean',
             root / 'evidence/r43-high-query-witness/rust-i/results/witness.json',
             root / 'evidence/r43-high-query-witness/rust-i/r18-stage.json']:
    pins[str(path.relative_to(repo))] = sha(path)
if a.record:
    (e / 'receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
    (e / 'SOURCE_PINS.json').write_text(json.dumps(pins, indent=2)+'\n')
    manifest = {str(f.relative_to(e)): sha(f) for f in sorted(e.rglob('*'))
                if f.is_file() and f.name != 'MANIFEST.json'}
    (e / 'MANIFEST.json').write_text(json.dumps(manifest, indent=2)+'\n')
assert json.loads((e / 'receipt.json').read_text()) == receipt
assert json.loads((e / 'SOURCE_PINS.json').read_text()) == pins
manifest = json.loads((e / 'MANIFEST.json').read_text())
assert set(manifest) == {str(f.relative_to(e)) for f in e.rglob('*')
                         if f.is_file() and f.name != 'MANIFEST.json'}
for name, digest in manifest.items():
    assert sha(e / name) == digest, name
print(json.dumps({'status': 'PASS', 'artifacts': len(manifest), 'new_theorems': 43,
                  'new_leaf_wall_seconds': receipt['new_leaf_wall_seconds'],
                  'all_selected_wall_seconds': receipt['all_selected_wall_seconds'],
                  'peak_rss_kib': receipt['peak_rss_kib'], 'full_privacy': False,
                  'new_sbf_measurement': False}, indent=2))
