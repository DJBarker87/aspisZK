#!/usr/bin/env python3
"""Scoped current-source proof and causal-strategy evidence; no global certificate."""
import json
from pathlib import Path
import re
import sys
import audit_soundness_proofs as evidence
from audit_causal_rows import checked_leaf
from three_helper_cover_checks import result as cover_checks

BASE = '1b8f72d9de123b16eb831754e58518e66a33d3f3'
LEAVES = [
    ('SharedInverseReplay', 'shared-inverse-replay-v*.log'),
    ('LineNormBuffer', 'line-norm-buffer-v*.log'),
    ('SelectedAmountEndpoint', 'selected-amount-endpoint-v*.log'),
    ('ScalarPowerSplit', 'scalar-power-split-v*.log'),
    ('ScalarPowerSplitInstances', 'scalar-power-split-instances-v*.log'),
    ('FiniteSumConcat', 'finite-sum-concat-v*.log'),
    ('FixedC1HelperReduction', 'fixed-c1-helper-v*.log'),
    ('ThreeHelperCover', 'three-helper-cover-v*.log'),
    ('ThreeHelperSelected', 'three-helper-selected-v*.log'),
]


def current_proofs():
    evidence.BASE = BASE
    leaves = [checked_leaf(*leaf) for leaf in LEAVES]
    for leaf in leaves:
        log = (evidence.ROOT / leaf['log']).read_text()
        paths = {}
        runners = []
        for expected, raw in re.findall(r'^([a-f0-9]{64})  (/[^\n]+)$', log, re.M):
            path = Path(raw)
            if path.suffix == '.sh':
                runners.append({'path':raw,'logged_sha256':expected,
                                'current_sha256':evidence.sha(path)})
                continue
            assert path.exists() and evidence.sha(path) == expected, (raw, expected)
            assert raw not in paths or paths[raw] == expected, ('changed during run', raw)
            paths[raw] = expected
        leaf['current_logged_source_cache_hashes_verified'] = len(paths)
        leaf['runner_versions'] = runners
        leaf['provenance_scope'] = (
            'runner pre/post equality plus current recorded-file hash audit'
            if 'PROVENANCE_UNCHANGED=true' in log else
            'runner pinned checks plus current recorded-file hash audit; see runner for pre/post coverage')
    return leaves


def strategy_evidence():
    path = evidence.EX / 'final-transport-strategy-v1.log'
    log = path.read_text()
    assert 'COMPILE_EXIT=0' in log and 'STRATEGY_EXIT=0' in log and BASE in log
    assert not re.search(r'panicked|AGGREGATE_RSS_STOP|error\[', log)
    for name in ('final_transport_strategy.rs', 'run_final_transport_strategy.sh'):
        source = evidence.EX / name
        assert log.count(f'{evidence.sha(source)}  {source}') == 2
    start = log.index('{"field":11,')
    result, _ = json.JSONDecoder().raw_decode(log[start:])
    assert result['direct_scalar_checks'] > 0
    assert result['states_with_changed_optimum'] > 0
    assert result['final_options'] == 11**4
    assert result['response0_options_per_claim'] == 11**2
    times = [float(x) for x in re.findall(r'^\s*([0-9.]+) real', log, re.M)]
    rss = [int(x) for x in re.findall(r'^\s*(\d+)\s+maximum resident set size', log, re.M)]
    swaps = [int(x) for x in re.findall(r'^\s*(\d+)\s+swaps$', log, re.M)]
    assert len(times) == len(rss) == len(swaps) == 2 and swaps == [0, 0]
    return {
        'log': str(path.relative_to(evidence.ROOT)), 'log_sha256': evidence.sha(path),
        'source_sha256': evidence.sha(evidence.EX / 'final_transport_strategy.rs'),
        'compile': {'exit':0,'wall_seconds':times[0],'peak_rss_bytes':rss[0],'swaps':swaps[0]},
        'strategy_run': {'exit':0,'wall_seconds':times[1],'peak_rss_bytes':rss[1],'swaps':swaps[1]},
        'result': result,
        'is_QM31_or_actual_payment_game': False,
        'exhaustive_over_all_first_responses': False,
        'claims_global_soundness_bound': False,
    }


def result():
    leaves = current_proofs()
    strategy = strategy_evidence()
    body = 697*16 + 52 + 24 + 22*621 + 2*296*26
    assert body == 40282
    return {
        'base_revision': BASE,
        'borrowed_formal_revision': '26a9cd4718aae9f9de7ef1c3394fb74a229085d5',
        'environment': 'Lean4.32.0 / pinned Mathlib81a5d257; serial cached leaves, -M7000 and7GiB process-tree guard; optimized bounded Rust reduced game',
        'leaves': leaves,
        'strategy_search': strategy,
        'three_helper_margin_checks': cover_checks(),
        'deterministic_endpoints': {
            'shared_inverse': 'single terminal inverse plus actual backward recurrence equals checked separate/joined field-list inversion, including rejection',
            'line_buffer': 'derived five coefficients, canonical half, ordered point/line zip, norm lists and shared reconstruction equal checked queried inversion; typed unit points, not mutable Rust/parser translation',
            'amounts': 'same lifted C1 table, modeled positivity pack and literal selected copy/range/conservation residuals imply positive decoded/raw transfer amounts,30bit bounds,natural conservation and u32 safety',
            'C1_helper_reduction': 'literal26+3 batch restricts on fixed C1 own-support to quadratic helper curve after affine normalization; wrong C1 point claim remains degree25/Laurent, not degree2',
            'three_helper_cover': 'generic code-valued quadratic curve on fixed supportD: fewer than3 Good parameters OR constructed3-coefficient code tuple covers ALL B-close candidates, when4B+delta<|D|; not actual accepted-mass or extractor theorem',
            'selected_helper_cover': 'actual earlyC1=some p derives own support≥245609; fewer than3 Good gammas OR constructed pre-gamma helper messages represent every original-code message with≤61338 raw bad fibres ON that support, using actual encoder/fibre equality and injectivity; no exact C1 outside support or accepted-mass assumption',
        },
        'new_probability_bound_for_actual_acceptance': None,
        'ledger': [
            {'event':'private semantic-C1 decoder failure GIVEN earlyC1=some p and stated public algebraic/access law',
             'status':'reuse prior private-c1-recovery-evidence.json unchanged; not a witness-validity theorem',
             'new_term':False,'relation_repairs_counted_here':0},
            {'event':'far accepted false ordinary/OOD/semantic claims',
             'status':'still unresolved; corrected causal reduced-game evidence and helper reduction do not supply QM31 bound',
             'bound':None},
            {'event':'individual selected amount residuals and same-table positive pack hold',
             'status':'deterministic strict-amount implication proved; acceptance-to-these-premises remains open',
             'probability_term':None},
            {'event':'actual earlyC1=some and a raw original-code candidate is≤61338 bad fibres on the derived C1 own support',
             'fixing_prefix':'C1 determines p/S; C2 determines helper curve/Good/constructed helper tuple before gamma; candidate may be adaptive',
             'status':'ThreeHelperSelected.early_cover constructs message representation in dense branch and retains fewer-than3 Good alternative; probability/image/row game not yet composed',
             'bound':None},
            {'event':'actual norm-buffer field/list construction to checked inverse',
             'status':'deterministic equality, not a probabilistic toolchain assumption',
             'probability_term':None},
        ],
        'remaining_accepted_failure_classes': [
            'earlyC1none AND specified checked-witness extractor fails',
            'correctly recovered coefficients but accepted false claims or failed selected semantic/copy/payment constraints',
            'remaining ownership,note/path,authoritative context and settlement witness completeness',
            'authentication/canonical fixed-word interpretation; actual code/matrix descent and decoder source',
            'opening/replay/private-sampler access; abort/fuel/missing response/cached-advance mismatch',
            'actual parser/optimized-machine/source-to-game coupling and resource-bounded Fiat-Shamir',
        ],
        'global_accepted_payment_extraction_failure': None,
        'remaining_global_error_allowance': None,
        'Fiat_Shamir_bound': None,
        'Fiat_Shamir_resources': ['oracle queries and prequeries','nonce/retry selection',
                                 'forks/restorations','extractor opening/replay calls',
                                 'running time','memory','sampler exhaustion'],
        'quantum_security_claim': False,
        'unlimited_offline_search_security_claim': False,
        'full_view_ZK_complete': False,
        'maximum_body_bytes': body,
        'new_proof_bytes':0,'new_verifier_operations':0,
        'new_complete_transaction_CU_or_prover_measurement':False,
        'production_changes':False,'grinding_credit_bits':0,
        'composition':'No396430 import, no duplicate relation-repair charge, no sum of inapplicable or overlapping local bounds. Unproved source correspondence has no invented numerical probability.',
    }


if __name__ == '__main__':
    out = result()
    if sys.argv[1:] == ['--check-recorded']:
        assert json.loads((evidence.ROOT/'helper-source-continuation-evidence.json').read_text()) == out
        print('Current-source helper/payment/query proofs and scoped causal search evidence match.')
    else:
        assert not sys.argv[1:]
        print(json.dumps(out, indent=2))
