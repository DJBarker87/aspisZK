#!/usr/bin/env python3
"""Step-4 attribution: every phase whose CU varies across profiled runs must be
covered by listed sites in the functions that execute in that phase."""
import json, re, sys
A, prof = sys.argv[1], json.load(open(sys.argv[2]))
PH = [  # (tx, phase regex, function regex, extra listed site ids)
 ('stage1', r'^r1:semantic$', r'r1_semantic|r1_wire|pair_forest_semantic_terminal|pair_forest_copy_terminal|state_only|semantic|sampler|circle|try_from_fn|public_bytes', ['S-CIRCLE', 'LOOP']),
 ('stage1', r'^r1:prepare$', r'Prepared|sampler|transcript|r0_transcript|QueryScan|prepared_claim|EbyKDot|fast_pairing|powers', ['S-QSCAN']),
 ('stage1', r'^r1:(merkle|query):', r'merkle_path|private_leaf|four_dots|query_with_geometry|accumulate|fold|BatchedWeights|QueryGeometry|fast_dots', []),
 ('stage1', r'^r1:(parsed|checkpoint-write)', r'View|parse|echeck|checkpoint|tx1|stage1|decode|validate|encode|first', []),
 ('stage2', r'^r1:parsed', r'r1_pool_adapter|decode|validate|encode|View|authenticate|scan_proof|reconstruct|asq8|stage2|pair_forest|payment|verifier_registry|lane', ['LOOP']),
 ('stage2', r'^r1:(checkpoint-read)', r'resume|Reader|powers|checkpoint|QueryGeometry|BatchedWeights|from_le', []),
 ('stage2', r'^r1:(merkle|query):', r'merkle_path|private_leaf|four_dots|query_with_geometry|accumulate|fold|BatchedWeights|fast_dots', []),
 ('stage2', r'^r1:(relation|final)', r'finish_relation|weights|Weights|polynomial|EbyKDot|fast_pairing|libra|scalar_factor|try_from_fn', []),
]
rows = []
for group, phases in prof.items():
    kind, split, tx = group.split('/')
    agg = json.load(open(f'{A}/{"stage1" if tx == "stage1" else "stage2"}-{kind}-agg.json'))
    byfn = dict(agg['extra_by_function'])
    for ph, v in phases.items():
        if not v['varies']: continue
        base = ph.split('#')[0]
        m = [p for p in PH if p[0] == tx and re.search(p[1], base)]
        if not m: rows.append(dict(group=group, phase=ph, range=v['max'] - v['min'], covered=False, why='no phase mapping')); continue
        fr = m[0][2]; listed = sum(x for f, x in byfn.items() if re.search(fr, f))
        rows.append(dict(group=group, phase=ph, range=v['max'] - v['min'], listed_site_max_in_phase_functions=listed,
                         extra_sites=m[0][3], covered=(v['max'] - v['min']) <= listed or bool(m[0][3])))
bad = [r for r in rows if not r['covered']]
json.dump(dict(rows=rows, uncovered=bad), open(sys.argv[3], 'w'), indent=1)
print('varying phases', len(rows), 'uncovered', len(bad)); [print(' ', r) for r in bad[:20]]
