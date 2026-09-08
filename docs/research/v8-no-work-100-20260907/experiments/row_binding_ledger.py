#!/usr/bin/env python3
"""Exact local ledger; emits JSON to stdout. Display bits are not certificates."""
from fractions import Fraction as F
from math import comb, log2
import json

K = (2**31 - 1)**4
T, Q, DEG = 262144, 22, 255
TARGET = F(1, 2**100)

def rational(v):
    return {"numerator": str(v.numerator), "denominator": str(v.denominator)}

def row(b):
    query = F(comb(b+DEG, Q), comb(T, Q))
    error = F(Q+3, K-1) + F(24, K) + query
    ceiling = TARGET-error
    return {"corrupt_fibres": b, "matching_cap_if_different_final": b+DEG,
            "query": rational(query), "local_joint_error": rational(error),
            "display_bits": log2(error.denominator)-log2(error.numerator),
            "local_below_2neg100": error <= TARGET,
            "target_budget_fraction": rational(error/TARGET),
            "ceiling_before_unsupported_terms": rational(ceiling),
            "actual_global_remaining_allowance": None,
            "status": "kernel-checked causal game; source refinement and global coverage unresolved"}

miss = F(comb(T-1,Q),comb(T,Q))
assert miss == 1-F(Q,T)
# Independent finite hockey-stick / product checks, not security estimation.
for t in range(2,31):
    for q in range(1,t):
        assert F(comb(t-1,q),comb(t,q)) == 1-F(q,t)
        for m in range(q,t+1):
            v = F(1)
            for j in range(q): v *= F(m-j,t-j)
            assert v == F(comb(m,q),comb(t,q))
body = 697*16 + 52 + 24 + 22*621 + 2*296*26
assert body == 40282
result = {
    "base_revision": "f8c2f7a949fdbb31431a104c8d29d34195594d98",
    "q": Q, "field_cardinality": str(K), "domain_fibres": T,
    "local_formula": "25/(k-1)+24/k+choose(B+255,22)/choose(262144,22)",
    "rows": [row(b) for b in (0,1,9301,10980,10981)],
    "single_corrupt_fibre_miss_conditioned_on_prefix": rational(miss),
    "single_corrupt_fibre_miss_scope": "fresh uniform distinct schedule; not complete acceptance probability",
    "wire": {"fixed_field_bytes":697*16, "root_bytes":52, "existing_nonce_bytes":24,
             "query_record_bytes":22*621, "max_frontier_bytes":2*296*26,
             "maximum_body_bytes":body, "repair_extra_bytes":0,
             "maximum_observed_fixture_body_bytes":39866},
    "repair_operations": {"extra_qm31_multiplications_for_scale_generation":1,
        "extra_challenges":0,"extra_rounds":0,"extra_proof_scalars":0,
        "complete_transaction_cu_delta":None,"sbf_stack_bound":None},
    "unapproved_controls": {"qm31_q23_body":41527,"quintic_q22_body":42984},
    "unbounded_raw_terms": ["no_pre_kappa_near_anchor", "aggregate_correct_component_or_semantic_extraction_failure",
                           "source_correspondence", "authentication", "replay_or_extractor_resource_failure",
                           "remaining_semantic_events"],
    "fiat_shamir_bound":None,"privacy_full_view_simulation":None,
    "grinding_security_credit_bits":0,
    "note":"No reuse of 396430; four relation repairs counted once in local formula. Not achieved V8 security."
}
print(json.dumps(result, indent=2))
