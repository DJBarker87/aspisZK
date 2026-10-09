#!/usr/bin/env python3
"""Current-source audit of the composed helper/claim and endpoint leaves."""
import json
from pathlib import Path
import re
import sys
import audit_soundness_proofs as evidence
from audit_causal_rows import checked_leaf
from helper_joint_ledger import result as ledger

BASE = 'e90e7338656f221c9a1bbde90d533ba94d002014'
LEAVES = [
    ('GenericOODClaimGame', 'generic-ood-claim-game-v*.log'),
    ('ThreeHelperClaimCover', 'three-helper-claim-cover-v*.log'),
    ('HelperJointGame', 'helper-joint-game-v*.log'),
    ('SelectedQueryBuffer', 'selected-query-buffer-v*.log'),
    ('SelectedOutputNotes', 'selected-output-notes-v*.log'),
    ('SelectedOutputPair', 'selected-output-pair-v*.log'),
]


def proofs():
    evidence.BASE = BASE
    leaves = [checked_leaf(*leaf) for leaf in LEAVES]
    for leaf in leaves:
        source = (evidence.EX / leaf['target']).read_text()
        assert not re.search(r'^\s*(axiom|sorry|admit)\b|\bby\s+(sorry|admit)\b', source, re.M)
        log = (evidence.ROOT / leaf['log']).read_text()
        assert 'LEAN_EXIT=0' in log
        paths, runners = {}, []
        for expected, raw in re.findall(r'^([a-f0-9]{64})  (/[^\n]+)$', log, re.M):
            path = Path(raw)
            if path.suffix == '.sh':
                runners.append({'path': raw, 'logged_sha256': expected,
                                'current_sha256': evidence.sha(path)})
                continue
            assert path.exists() and evidence.sha(path) == expected, (raw, expected)
            assert raw not in paths or paths[raw] == expected, ('changed during run', raw)
            paths[raw] = expected
        leaf['current_logged_source_cache_hashes_verified'] = len(paths)
        leaf['runner_versions'] = runners
        leaf['provenance_scope'] = (
            'runner pre/post equality plus current recorded-file hash audit'
            if 'PROVENANCE_UNCHANGED=true' in log else
            'runner pinned pre/post checks plus current recorded-file hash audit')
    return leaves


def result():
    return {
        'base_revision': BASE,
        'borrowed_formal_revision': '26a9cd4718aae9f9de7ef1c3394fb74a229085d5',
        'environment': 'Lean4.32.0 / Mathlib81a5d257, serial cached focused leaves, -M7000 and7GiB aggregate child RSS guard',
        'leaves': proofs(),
        'ledger': ledger(),
        'new_claim_endpoint': {
            'theorem': 'HelperJointGame.early_c1_wrong_claim_bound',
            'scope': 'actual selected-index compact FIELD game, supported on folded final distance<=15334, conditional on literal earlyC1=some p26 and a wrong ordinary/OOD C1 claim to that same early p26',
            'no_helper_or_quotient_candidate_membership_premise': True,
            'earlyC1_some_is_an_explicit_prerequisite': True,
            'not_actual_Rust_or_authenticated_replay_acceptance': True,
            'not_all_near_acceptance': True,
            'not_payment_extraction_failure': True,
        },
        'query_endpoint': 'actual selected query indices construct typed same-point values/base/norm buffers; inverse success derives exact pointwise fold residual and queried poles reject; no supplied buffer/reciprocal/polynomiality equality',
        'payment_endpoint': 'literal recipient/change decoder fields and individual selected modeled gate/copy/initial/tail/public-binding residuals derive both output note openings; independent public values are inputs, not authenticated by this theorem',
        'output_pair_endpoint': 'same-table output openings plus selected row1018 occupancy/copy/block33 residuals derive nonzero change sentinel, success of modeled checked two_outputs construction, and row539 ordered node hash; not assumed successful Rust compilation or independently authenticated context',
        'regressions_preserved_without_unchanged_replay': [
            'original and paired far root products', 'high-J own versus same-support distinction',
            'T512 invalid image and zero-fold image kernel',
            'unshifted row and late-inactive timing failure',
            'shifted query cancellation and sequential relation repairs',
            'harmless out-of-radius D corruption',
            'mask-only full26 none versus recoverable semantic16',
            'degree25 C1 error survives quadratic-helper normalization',
            'strict quadratic-cover support margin',
            'adaptive final changes the carried scalar as well as query matches'],
        'production_changes': False,
        'global_100_bit_certificate': False,
        'new_prover_SBF_or_complete_transaction_CU_measurement': False,
    }


if __name__ == '__main__':
    out = result()
    if sys.argv[1:] == ['--check-recorded']:
        assert json.loads((evidence.ROOT / 'helper-joint-continuation-evidence.json').read_text()) == out
        print('Composed helper/claim, output-note and selected-query evidence matches current source.')
    else:
        assert not sys.argv[1:]
        print(json.dumps(out, indent=2))
