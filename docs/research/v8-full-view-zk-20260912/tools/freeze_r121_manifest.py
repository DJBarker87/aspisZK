#!/usr/bin/env python3
"""Freeze only the twelve new leaves, after their focused preflights."""
import argparse
import hashlib
import json
import re
from pathlib import Path
from audit_r121_source import audit

parser = argparse.ArgumentParser()
parser.add_argument('--check', action='store_true')
args = parser.parse_args()
root = Path(__file__).resolve().parent.parent
audit()
names = ['TwoSwapSourceTable', 'TwoSwapSourceWeights', 'TwoSwapSourceG',
         'TwoSwapSourceFixed', 'TwoSwapResidualModel', 'TwoSwapResidualSource',
         'TwoSwapSourceMinor', 'TwoSwapResidualPolynomial', 'TwoSwapResidualDegree',
         'TwoSwapResidualNonzero', 'TwoSwapChordScale', 'TwoSwapSourceGate']
seen = set()
records = []
for name in names:
    path = root / 'lean/AspisV8R19' / (name + '.lean')
    s = path.read_text()
    assert not re.search(r'\b(sorry|admit|native_decide|trace_state)\b|^\s*axiom\s', s, re.M)
    assert 'T163SourceTable.order' not in s and 'SparseHighWitness' not in s
    for dependency in re.findall(r'^import AspisV8R19\.(\w+)$', s, re.M):
        if dependency in names:
            assert dependency in seen, (name, dependency)
    seen.add(name)
    records.append({'target': 'AspisV8R19/' + name,
                    'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                    'axioms_audits': len(re.findall(r'^#print axioms ', s, re.M))})
data = {'base_revision': '1cf29982431cc456ec7d0b670b6c221366e557b4',
        'toolchain': 'leanprover/lean4:v4.32.0', 'targets': records,
        'focused_preflights_completed': True,
        'no_new_generated_numeric_certificate': True,
        'symbolic_degree_and_inverse_proofs': True,
        'next_bridge': 'TwoSwapSourceGate.source_nonsingular_iff',
        'rust_word_refinement': False, 'adaptive_probability_bound': False,
        'full_privacy': False, 'full_soundness': False}
output = Path(__file__).with_name('r121-release-manifest.json')
if args.check:
    assert json.loads(output.read_text()) == data
else:
    assert not output.exists()
    output.write_text(json.dumps(data, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'targets': len(records),
                  'axioms_audits': sum(r['axioms_audits'] for r in records)}))
