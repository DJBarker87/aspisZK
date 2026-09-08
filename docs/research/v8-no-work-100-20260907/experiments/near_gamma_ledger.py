#!/usr/bin/env python3
"""Exact local ledger; unknown global terms deliberately remain symbolic."""
from fractions import Fraction
from math import comb, log2
import json

def rational(x):
    return {"numerator": str(x.numerator), "denominator": str(x.denominator)}

def main():
    k = (2**31 - 1)**4
    query = Fraction(comb(9556, 22), comb(262144, 22))
    product = Fraction(1)
    for i in range(22):
        product *= Fraction(9556-i, 262144-i)
    assert query == product
    small = Fraction(63, k-1)
    dense = Fraction(53, k-1) + Fraction(24, k) + query
    bound = max(small, dense)
    assert bound == dense < Fraction(1, 2**105)
    assert 9557*comb(64, 29) < 113328*comb(61, 29)
    body = {"canonical_fixed_fields": 697*16, "roots": 52,
            "existing_nonce_fields": 24, "queries": 22*621,
            "maximum_binary_frontiers": 2*296*26}
    assert sum(body.values()) == 40282
    terms = [
        ("component_row_cancellation", "pre-gamma tuple and 87 point claims", "nonzero gamma", Fraction(28,k-1)),
        ("shifted_ordinary_row_cancellation", "anchor and inactive fixed before kappa", "nonzero kappa", Fraction(3,k-1)),
        ("first_relation_repair", "response0 before alpha0", "whole-field alpha0", Fraction(6,k)),
        ("different_final_evades_queries", "actual final before schedule", "uniform distinct q-subset", query),
        ("shifted_query_batch_cancellation", "prior and residuals before rho", "nonzero rho", Fraction(22,k-1)),
        ("later_relation_repairs", "each response before next alpha", "whole-field alpha1..3", Fraction(18,k)),
    ]
    assert sum((t[3] for t in terms), Fraction()) == dense
    out = {
        "base_revision": "a33f4f6b2a11b52680597a5f849a63fe221f3fcb",
        "evidence_status": "arithmetic verified; modular Lean lemmas; actual source endpoint unresolved",
        "experiment": "ideal causal near-anchor component-point binding; no grinding credit",
        "parameters": {"field_cardinality": str(k), "q":22, "B":9301, "T":262144, "final_degree":255},
        "small_good_branch": rational(small),
        "dense_good_branch": rational(dense),
        "local_max_bound": {**rational(bound), "bits_display_only": log2(bound.denominator)-log2(bound.numerator)},
        "terms": [{"event":e, "fixing_prefix":p, "fresh_law":l, "error":rational(v)} for e,p,l,v in terms],
        "overlap_rule": "24/k already includes all four relation repairs. Small/dense branches use max. No historical 396430 term imported.",
        "local_budget_fraction_used": rational(bound*2**100),
        "headroom_after_this_local_charge_only": rational(Fraction(1,2**100)-bound),
        "global_remaining_allowance": None,
        "global_remaining_formula": "2^-100 - local_charge - U_no_anchor - U_tuple_to_witness - E_other_justified",
        "unknowns": {"U_no_anchor": None, "U_tuple_to_witness": None,
            "authentication": None, "source_and_replay_refinement": None,
            "FS_resource_bound": None, "full_view_ZK": None, "complete_transaction_CU": None},
        "own_support": {"maximum_bad_fibres":16535, "minimum_good_fibres":245609, "minimum_good_symbols":982436},
        "wire_sections_bytes": body, "maximum_body_bytes": sum(body.values()),
        "new_transmitted_values": 0,
        "unapproved_controls_bytes": {"QM31_q23":41527, "quintic_q22":42984},
        "measurements": {"full_prover_time": None, "prover_peak_RSS": None, "search_time": None, "SBF_CU": None},
        "privacy_status": "separate full-view simulation obligation; unchanged by this proof continuation"
    }
    print(json.dumps(out, indent=2))

if __name__ == "__main__":
    main()
