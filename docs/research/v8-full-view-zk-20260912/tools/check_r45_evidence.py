#!/usr/bin/env python3
"""Freeze/check focused R45 receipts without replaying unchanged builds."""
import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

p = argparse.ArgumentParser()
p.add_argument('--record', action='store_true')
a = p.parse_args()
root = Path(__file__).resolve().parent.parent
repo = root.parents[2]
e = root / 'evidence/r45-source-mask-transport'
base = '0f9c5688fbcc1fa94317a01dce52b63f23fb2315'
checks = [
    ('b', 'AspisV8R19/T163SourceTable', 10, True),
    ('b', 'AspisV8R17/LegalMaskCoordinates', 5, False),
    ('b', 'AspisV8R19/SourceMaskTransport', 11, True),
    ('c', 'AspisV8R19/RetainedSparseShift', 14, False),
    ('c', 'AspisV8R17/ScatterDual', 3, False),
    ('e', 'AspisV8R19/SourceNaturalShift', 6, True),
    ('f', 'AspisV8R17/SourceGatherLoop', 5, False),
    ('f', 'AspisV8R17/ChordDual', 3, False),
    ('g', 'AspisV8R19/SourceChordEvaluation', 8, True),
    ('i', 'AspisV8R19/SourceEncodedOpening', 8, True),
    ('j', 'AspisV8R19/SourceMaskBoundary', 3, True),
]

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def metrics(path, audits):
    text = path.read_text()
    assert '\tExit status: 0' in text and '\tSwaps: 0' in text
    assert 'sorryAx' not in text and 'error:' not in text
    found = re.findall(r'depends on axioms: \[([^]]*)\]', text)
    assert len(found) == audits, (path, len(found), audits)
    for ax in found:
        assert set(re.sub(r'\s', '', ax).split(',')) <= {
            'propext', 'Classical.choice', 'Quot.sound'}
    rss = int(re.search(r'Maximum resident set size \(kbytes\): (\d+)', text).group(1))
    ts = re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)', text).group(1).split(':')
    return {'exit': 0, 'swaps': 0, 'peak_rss_kib': rss,
            'wall_seconds': round(sum(float(t)*60**i for i, t in enumerate(reversed(ts))), 2),
            'axioms_audited': audits}

for name in ('generate_r45_transport.py', 'extract_r45_sparse_shift.py'):
    subprocess.run([sys.executable, str(root/'tools'/name), '--check'], check=True)
records = json.loads((e/'lean-j/metadata.json').read_text())
assert len(records) == 222
for r in records:
    assert r['exit'] == 0 and r['toolchain'] == 'leanprover/lean4:v4.32.0'
    assert sha(root/'lean'/(r['target_name']+'.lean')) == r['source_sha256']
previous = json.loads((root/'evidence/r44-normalized-query-section/SOURCE_PINS.json').read_text())
for name, digest in previous.items():
    assert sha(repo/name) == digest, name

results = {}
for letter, name, count, new in checks:
    results[name] = metrics(e/f'lean-{letter}/{Path(name).name}.log', count)
    r = next(r for r in records if r['target_name'] == name)
    assert r['base_revision'] == base
    assert f'/aspis-r45-lean-20260929-{letter}/lib/' in r['command'][6]
    if new:
        source = (root/'lean'/(name+'.lean')).read_text()
        assert len(re.findall(r'^theorem ', source, re.M)) == count
        assert not re.search(r'\b(sorry|axiom|native_decide|maxHeartbeats|maxRecDepth|norm_num)\b', source)

# Preserve the failed focused predecessors. None was cured by raising limits.
for letter, name in [('a','T163SourceTable'),('c','SourceNaturalShift'),
                     ('d','SourceNaturalShift'),('f','SourceChordEvaluation'),
                     ('h','SourceEncodedOpening')]:
    assert '\tExit status: 1' in (e/f'lean-{letter}/{name}.log').read_text()

receipt = {
    'base_revision': base, 'new_theorems': sum(n for _,_,n,new in checks if new),
    'retained_theorem_audits': sum(n for _,_,n,new in checks if not new),
    'final_cache_objects': len(records), 'targets': results,
    'resources': {'MemoryHigh':'3G', 'MemoryMax':'5G', 'MemorySwapMax':0,
                  'TasksMax':128, 'max_simultaneous_reservation_gib':5},
    'new_leaf_wall_seconds': round(sum(results[n]['wall_seconds'] for _,n,_,new in checks if new),2),
    'all_selected_wall_seconds': round(sum(r['wall_seconds'] for r in results.values()),2),
    'peak_rss_kib': max(r['peak_rss_kib'] for r in results.values()),
    'source_pinned_T163_roundtrip': True,
    'legal_balanced_G_correction': True,
    'G_active_coordinates_required_zero': False,
    'all_271_sparse_coins_preserved': True,
    'source_shaped_chord_natural_evaluation': True,
    'interleaved_1024_encoded_OOD_zeros': True,
    'quotient_image_tail_and_truncation': True,
    'Rust_normalization_loop_refinement': False,
    'actual_circle_raw_evaluator_composition': False,
    'all_residual_source_equations': False,
    'new_fixed_query_polynomial_degree': False,
    'source_shared_oracle_law': False,
    'full_privacy': False, 'verifier_changed': False,
    'new_Rust_execution': False, 'new_SBF_measurement': False,
}
pins = {str((root/'lean'/(r['target_name']+'.lean')).relative_to(repo)):r['source_sha256'] for r in records}
extras = [root/'tools'/name for name in ('run_r45_lean.py','generate_r45_transport.py','extract_r45_sparse_shift.py')]
extras += [repo/'AspisFormal/AspisFormal/V5GoodGateSparseShift.lean',
           root/'evidence/r36-source-residual-model/source/docs/research/v8-no-work-100-20260907/experiments/r17_basis_tables.rs',
           root/'evidence/r31-sparse-g-inverse/source/docs/research/v8-no-work-100-20260907/experiments/r28_source_helpers.rs',
           root/'evidence/r43-high-query-witness/rust-i/r18-stage.json']
for path in extras:
    pins[str(path.relative_to(repo))] = sha(path)
if a.record:
    (e/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    (e/'SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
    manifest = {str(f.relative_to(e)):sha(f) for f in sorted(e.rglob('*')) if f.is_file() and f.name!='MANIFEST.json'}
    (e/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
assert json.loads((e/'receipt.json').read_text()) == receipt
assert json.loads((e/'SOURCE_PINS.json').read_text()) == pins
manifest = json.loads((e/'MANIFEST.json').read_text())
assert set(manifest) == {str(f.relative_to(e)) for f in e.rglob('*') if f.is_file() and f.name!='MANIFEST.json'}
for name, digest in manifest.items():
    assert sha(e/name) == digest, name
print(json.dumps({'status':'PASS','artifacts':len(manifest),
    **{k:receipt[k] for k in ('new_theorems','retained_theorem_audits',
       'new_leaf_wall_seconds','all_selected_wall_seconds','peak_rss_kib','full_privacy','new_SBF_measurement')}},indent=2))
