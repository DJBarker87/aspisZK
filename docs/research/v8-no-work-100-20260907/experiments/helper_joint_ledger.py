#!/usr/bin/env python3
"""Exact event-scoped arithmetic for the constructed helper/joint game.

Display logarithms are not certificates. Rational comparisons below certify
the stated integer-bit brackets. No global extraction or FS budget is filled.
"""
from decimal import Decimal, localcontext
from fractions import Fraction
from math import comb, prod
import json


def choose_ratio(m, q, total):
    assert 0 <= m <= total and 0 <= q <= total
    return Fraction(comb(m, q), comb(total, q))


def packed(value):
    with localcontext() as ctx:
        ctx.prec = 70
        number = Decimal(value.numerator) / Decimal(value.denominator)
        bits = -(number.ln() / Decimal(2).ln()) if number else None
    return {'numerator': str(value.numerator), 'denominator': str(value.denominator),
            'decimal_display': str(number), 'bits_display': str(bits)}


def result():
    # Independent multiplicative calculation, including empty schedules and
    # too-small matching sets. These are finite identity checks, not security
    # experiments and not an extrapolation from a small field.
    checks = 0
    for total in range(1, 17):
        for q in range(total + 1):
            for m in range(total + 1):
                alternate = (prod(Fraction(m-i, total-i) for i in range(q))
                             if m >= q else Fraction(0))
                assert choose_ratio(m, q, total) == alternate
                checks += 1
    k, q, total, radius = (2**31-1)**4, 22, 262144, 15334
    raw_radius, own_floor, overlap = 61338, 245609, 256
    assert 4*radius + 2 == raw_radius
    assert 4*raw_radius + overlap < own_floor
    assert 5*radius + 255 < total
    local_relation = Fraction(q+3, k-1) + Fraction(24, k)
    sparse = Fraction(2, k-1) + local_relation
    dense = Fraction(28, k-1) + local_relation
    assert sparse <= dense
    assert Fraction(1, 2**118) < dense < Fraction(1, 2**117)
    assert Fraction(1, 2**119) < sparse < Fraction(1, 2**118)
    # Far-final pointwise query-only control, NOT actual scalar acceptance,
    # an extraction failure, or a sufficient global security estimate.
    far_query = choose_ratio(total-radius-1, q, total)
    assert far_query > Fraction(1, 4)
    body = 697*16 + 52 + 24 + q*621 + 2*296*26
    assert body == 40282
    return {
        'base_revision': 'e90e7338656f221c9a1bbde90d533ba94d002014',
        'field_order': str(k), 'queries': q, 'initial_symbols': 1048576,
        'final_positions': total, 'supported_final_distance_at_most': radius,
        'raw_bad_on_C1_own_support_at_most': raw_radius,
        'C1_own_support_floor': own_floor, 'code_complete_fibre_overlap_cap': overlap,
        'independent_choose_ratio_checks': checks,
        'ideal_law': 'Gamma/kappa/tau/rho fresh uniform nonzero QM31; each alpha fresh uniform QM31; uniform distinct q-subset conditional on complete query prefix',
        'sparse_Good_branch': {
            'event': 'actual compact relation acceptance AND final distance<=15334; earlyC1=some p; fixed helper Good has cardinality<3',
            'bound': packed(sparse), 'formula': '2/(k-1)+(q+3)/(k-1)+24/k'},
        'dense_wrong_claim_branch': {
            'event': 'same supported compact acceptance with any wrong fixed ordinary component claim or component OOD answer relative to the one constructed pre-gamma tuple',
            'bound': packed(dense), 'formula': '28/(k-1)+(q+3)/(k-1)+24/k',
            'tuple_union_multiplier': 1, 'claim_union_multiplier': 1},
        'composition': {
            'gamma': 'sparse and dense cover cases are fixed before gamma, not overlapping bad events to add',
            'image_or_row': 'pre-kappa image-invalid and image-valid/wrong-row partition; root ceilings2 or3, uniformly3; not2+3',
            'relation_repairs': 'four degree-six sequential repairs counted once as24/k',
            'query_batch': 'shifted degree-q rho discrepancy counted as q/(k-1)',
            'sparse_alpha': 'at most3 eligible alpha values; bounded by the same local ceiling, not added again',
            'old_396430_inventory_imported': False},
        'far_query_only_control': {
            'matching_at_most': total-radius-1, 'ratio': packed(far_query),
            'scope': 'pointwise queries only at a fixed pre-query prefix, not scalar acceptance or extraction failure',
            'proves_100_bits': False},
        'remaining_global_terms': {
            'accepted_far_wrong_claims_or_extraction_failure': None,
            'earlyC1_none_and_checked_extraction_failure': None,
            'acceptance_to_individual_early_semantic_and_copy_constraints': None,
            'complete_payment_context_settlement_endpoint': None,
            'authenticated_openings_private_sampler_and_replay': None,
            'parser_machine_source_game_correspondence': None,
            'resource_bounded_Fiat_Shamir': None},
        'global_error': None, 'remaining_global_allowance': None,
        'full_view_adaptive_ZK_complete': False,
        'maximum_proof_body_bytes': body, 'new_proof_bytes': 0,
        'new_verifier_operations': 0, 'new_CU_or_prover_measurement': False,
        'grinding_credit_bits': 0, 'quantum_security_claim': False,
    }


if __name__ == '__main__':
    print(json.dumps(result(), indent=2))
