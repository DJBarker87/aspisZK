#!/usr/bin/env python3
"""Current-source proof/provenance ledger for private C1 recovery continuation."""
import json
from pathlib import Path
import re
import sys
from fractions import Fraction
import audit_soundness_proofs as evidence
from audit_causal_rows import checked_leaf
from private_sample_checks import result as sample_result

BASE = '113dc5dacbf630c234cc6498385913507c171f8f'
LEAVES = [
    ('PrivateSampleMoment', 'private-sample-moment-v*.log'),
    ('EarlyC1GaoRecovery', 'early-c1-gao-v*.log'),
    ('EarlyC1SampleGame', 'early-c1-sample-game-v*.log'),
    ('SelectedSparseMle', 'selected-sparse-mle-v*.log'),
    ('QueriedInverse', 'queried-inverse-v*.log'),
    ('QueriedResidual', 'queried-residual-v*.log'),
]


def result():
    evidence.BASE = BASE
    sample = sample_result()
    bound = sample['bound']
    e = Fraction(int(bound['numerator']), int(bound['denominator']))
    assert e < Fraction(1, 2**134)
    leaves = [checked_leaf(*leaf) for leaf in LEAVES]
    for leaf in leaves:
        log = (evidence.ROOT / leaf['log']).read_text()
        paths = {}
        runner_versions = []
        for expected, raw in re.findall(r'^([a-f0-9]{64})  (/[^\n]+)$', log, re.M):
            path = Path(raw)
            if path.suffix == '.sh':
                runner_versions.append({'path':raw,'logged_sha256':expected,
                                        'current_sha256':evidence.sha(path)})
                continue
            assert path.exists() and evidence.sha(path) == expected, (path, expected)
            assert raw not in paths or paths[raw] == expected, ('changed during run',raw)
            paths[raw] = expected
        leaf['current_logged_source_cache_hashes_verified'] = len(paths)
        leaf['runner_versions'] = runner_versions
        leaf['provenance_scope'] = (
            'runner pre/post equality plus current recorded-file hash audit'
            if 'PROVENANCE_UNCHANGED=true' in log else
            'runner pinned checks and current recorded-file hash audit; see runner for pre/post coverage')
    return {
        'base_revision': BASE,
        'borrowed_formal_revision': '26a9cd4718aae9f9de7ef1c3394fb74a229085d5',
        'environment': 'Lean4.32.0 / Mathlib81a5d257c8e410db227a6665ed08f64fea08e997; serial cached leaves;7GiB RSS guard;-M7000;zero swaps',
        'leaves': leaves,
        'private_sample': sample,
        'ledger': [{
            'event': 'arbitrary acceptance AND semantic coefficient decoder does not recover earlyC1 projection, GIVEN earlyC1=some p and explicit public algebraic interfaces',
            'fixing_prefix': 'received C1 and mathematical p determined at C1 prefix, before fresh private extractor sample; no final-distance premise',
            'challenge': 'fresh uniform513-subset of262144 complete fibres',
            'theorem': 'EarlyC1SampleGame.accepted_coefficient_failure_bound',
            'bound': bound,
            'scope': 'kernel-checked mathematical decoder/count composition; numerical comparison arithmetic verified; canonical/source/replay/private-sampler instantiation incomplete',
            'decoder_input_contains_p': False,
            'assumes_successful_decoder': False,
            'column_union_factor': 1,
            'four_relation_repairs_counted_here': 0,
            'conditioning': 'bounds joint accepted failure in original sampling law, not conditional uniformity after acceptance',
        }],
        'source_interface_progress': {
            'payment': 'actual modeled sparse scan, bounded Boolean table lookup and zero-carry successor feed same-table row1014 positive pack; not acceptance-to-constraints or Rust-machine translation',
            'queries': 'checked nested-norm inverse model and returned base-fold inverses connect queried quotients/residuals; zero queried poles reject; parser/Vec/limb/source execution refinement still separate',
        },
        'remaining_events': [
            'actual authentication, fixed-word interpretation, canonical M31 descent, public encoder/matrix instantiation',
            'actual private-opening/replay access; abort/fuel/missing responses/challenge mismatches; sampler exhaustion',
            'earlyC1none with failed checked witness extraction, especially far finals',
            'far accepted wrong ordinary/OOD/semantic C1 claims even when earlyC1some',
            'correct recovered coefficients but selected semantic/copy/payment/context/settlement validator not justified',
            'actual verifier/parser/optimized-field/source coupling and resource-bounded Fiat-Shamir',
        ],
        'composition': 'no automatic sum with older117/105bit local events; private sample error is distinct but full precedence/source/extractor accounting remains unproved; no396430 import or duplicated24/k',
        'global_accepted_payment_extraction_failure': None,
        'remaining_global_error_allowance': None,
        'Fiat_Shamir_bound': None,
        'Fiat_Shamir_resources': ['oracle queries/prequeries','nonce/retry selection','forks/restores','extractor oracle/replay calls','running time','memory'],
        'full_view_ZK_complete': False,
        'maximum_body_bytes': sample['body_bytes'],
        'extra_body_bytes': 0, 'extra_verifier_operations': 0,
        'new_Rust_SBF_or_prover_measurement': False,
        'production_changes': False, 'grinding_credit_bits': 0,
        'unlimited_offline_or_quantum_claim': False,
        'next_decisive_experiment': 'fixed earlyC1 with one false semantic point claim, legal adaptive C2/OOD/farfinal/compact responses; bound accepted wrong-claim mass while preserving validC1/farD control',
    }


if __name__ == '__main__':
    out = result()
    if sys.argv[1:] == ['--check-recorded']:
        assert json.loads((evidence.ROOT/'private-c1-recovery-evidence.json').read_text()) == out
        print('Private C1 decoder/count, payment/query interfaces and scoped evidence match.')
    else:
        assert not sys.argv[1:]
        print(json.dumps(out, indent=2))
