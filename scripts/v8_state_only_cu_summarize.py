#!/usr/bin/env python3
"""Validate five paired runs. Usage: script RESULTS_DIR [rate256-q22]."""
import json
from pathlib import Path
import sys

directory = Path(sys.argv[1])
profile = sys.argv[2] if len(sys.argv) > 2 else 'rate512-q16'
assert profile in ('rate512-q16', 'rate256-q22')
label = 'unmined diagnostic path (PoW rejection disabled)'
runs = [json.loads((directory / f'{profile}-run-{i}.json').read_text()) for i in range(1, 6)]
first = runs[0]
for i, run in enumerate(runs, 1):
    assert run['run'] == i and run['label'] == label
    assert run['simulation_execution_agree'] and run['identical_to_first_run']
    assert run['proof_account_unchanged'] and run['verifier_completed']
    assert run['simulation'] == run['execution']
    assert run['execution']['error'] is None
    for key in ('phase_markers', 'verifier_cu', 'proof_sha256', 'public_sha256',
                'elf_sha256', 'runtime', 'source_revision', 'txv1_bytes'):
        assert run[key] == first[key], (i, key)
    assert run['runtime']['limit_cu'] == 1_400_000
    assert run['runtime']['release_build']

points = {p['phase']: p['remaining_cu'] for p in first['phase_markers']}
def cost(before, after):
    return points[before] - points[after]

terminal = cost('transcript-sumcheck', 'terminal')
mask = cost('terminal-composition-equality', 'terminal-mask')
phases = {
    'transcript_sumcheck': cost('parsed', 'transcript-sumcheck'),
    'terminal_excluding_mask': terminal - mask,
    'mask_terminal': mask,
    'relation_final_polynomial': cost('terminal', 'relation-final-polynomial'),
    'merkle_opening_authentication': cost('relation-final-polynomial', 'merkle-openings'),
    'fri_query_arithmetic': cost('merkle-openings', 'fri-queries'),
}
phases['account_public_parse_return_and_other_markers'] = first['verifier_cu'] - sum(phases.values())
assert sum(phases.values()) == first['verifier_cu']
audit_name = 'pow-omission-audit.json' if profile == 'rate512-q16' else f'{profile}-pow-omission-audit.json'
audit = json.loads((directory / audit_name).read_text())
assert audit['measured_elf_sha256'] == first['elf_sha256']
assert audit['identical_text_sections']
pow_allowance = audit['omission_upper_bound_cu']
summary = {
    'label': label, 'source_revision': first['source_revision'], 'runs': 5,
    'all_simulations_and_executions_accepted_and_agreed': True,
    'shape': first['shape'], 'query_count': first['query_count'],
    'proof_bytes': first['proof_bytes'], 'txv1_bytes': first['txv1_bytes'],
    'txv1_headroom_to_4096_bytes': 4096 - first['txv1_bytes'],
    'verifier_cu': first['verifier_cu'], 'phase_cu': phases,
    'terminal_including_mask_cu': terminal,
    'headroom_to_1300000_cu': 1_300_000 - first['verifier_cu'],
    'headroom_to_1400000_cu': 1_400_000 - first['verifier_cu'],
    'pow_omission_upper_bound_cu_same_compiled_replay': pow_allowance,
    'verifier_plus_pow_omission_upper_bound_cu': first['verifier_cu'] + pow_allowance,
    'instrumentation_included': True,
    'raw_diagnostic_harness_cu': first['execution']['cu'],
    'production_transaction_cu': None,
    'v7_historical_comparison': {
        'verifier_cu': 1_084_738, 'transaction_cu': 1_218_972, 'txv1_bytes': 1043,
        'source': 'docs/research/v7-first-cap203-scan-cu-fix-20260902.md:82-83',
        'remeasured': False, 'same_profile': False,
    },
}
if profile == 'rate256-q22':
    rejection = json.loads((directory / f'{profile}-reject-1.json').read_text())
    assert rejection['expected_rejection']
    assert rejection['simulation'] == rejection['execution']
    assert rejection['execution']['error'] == 'InstructionError(2, InvalidInstructionData)'
    assert rejection['elf_sha256'] == first['elf_sha256']
    assert rejection['original_proof_sha256'] == first['proof_sha256']
    assert rejection['mutation']['changed_bytes'] == 1 and rejection['mutation']['canonical_after']
    rejected_phases = {p['phase'] for p in rejection['phase_markers']}
    assert 'relation-final-polynomial' in rejected_phases and 'merkle-openings' not in rejected_phases
    previous = json.loads((directory / 'summary.json').read_text())
    summary['delta_from_m1_rate512_q16'] = {
        'proof_bytes': first['proof_bytes'] - previous['proof_bytes'],
        'verifier_cu': first['verifier_cu'] - previous['verifier_cu'],
        'phase_cu': {k: v - previous['phase_cu'][k] for k, v in phases.items()},
    }
    summary['model_correspondence_established'] = False
    summary['rejection_witness_verified'] = True
name = 'summary.json' if profile == 'rate512-q16' else f'{profile}-summary.json'
(directory / name).write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps(summary, indent=2))
