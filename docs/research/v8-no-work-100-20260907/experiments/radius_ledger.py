#!/usr/bin/env python3
"""Exact NEW boundary diagnostic; consume, do not replay, the near ledger.

Run from any directory. Output is deterministic JSON. --check compares the
committed result. No Monte Carlo or work-normalised security estimate.
"""
import argparse
from decimal import Decimal, localcontext
from fractions import Fraction
from hashlib import sha256
import json
from math import comb
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def rational(x):
    return {"numerator": str(x.numerator), "denominator": str(x.denominator)}


def results():
    t, s, cutoff, delta, q = 262144, 9302, 9301, 256, 22
    miss = Fraction(comb(t-s, q), comb(t, q))
    product = Fraction(1)
    for j in range(q):
        product *= Fraction(t-s-j, t-j)
    assert miss == product
    assert t-s-delta == 252586 and 2*s+delta < t
    with localcontext() as ctx:
        ctx.prec = 60
        display = str(Decimal(miss.numerator)/Decimal(miss.denominator))
    inherited_bytes = (ROOT / "near-gamma-results.json").read_bytes()
    inherited = json.loads(inherited_bytes)
    return {
        "base_revision": "954b88948ba7a4aab809ec6d21e3524af033f148",
        "status": "arithmetic verified; generic geometry Lean-proved; no global recovery bound",
        "boundary": {
            "T": t, "s": s, "cutoff": cutoff, "distinct_codeword_fibre_overlap_cap": delta,
            "other_codeword_min_distance": t-s-delta,
            "unique_nearest_gap": t-(2*s+delta),
            "query_miss": rational(miss), "query_miss_decimal_display": display,
            "challenge_law": "fresh uniform distinct q22 subset conditional on fixed corruption support",
            "scope": "query diagnostic, not complete-verifier acceptance or a forgery",
            "code_applicability": "generic overlap theorem; concrete quotient/index port not completed"
        },
        "inherited_near_result": {
            "file": "near-gamma-results.json", "sha256": sha256(inherited_bytes).hexdigest(),
            "local_bound": inherited["local_max_bound"],
            "scope": "supported near bad-binding event in ideal game, not all near extraction failure",
            "replayed": False,
            "overlap": "four degree-six repairs already charged; do not add another 24/k"
        },
        "accounting": {
            "target": "Pr[A AND NOT X_checked_within_resources]",
            "rejected_target": "Pr[A AND no_9301_anchor] as a proxy for extraction failure",
            "conditional_formula": "after source coupling: E_near + Pr[A AND NOT X AND NOT B_near] + separately coupled layers",
            "global_remaining_allowance": None,
            "near_subtraction_is_release_budget": False,
            "unknown_bounds": {
                "accepted_residual_recovery_failure": None,
                "near_correct_binding_but_no_checked_witness": None,
                "tuple_to_witness_coverage": None,
                "authentication": None,
                "replay_or_fuel_failure": None,
                "FS_resources_and_extraction": None
            },
            "missing_deterministic_bridges": [
                "complete repaired verifier to causal game constructor",
                "concrete quotient/image/index code port",
                "C1 recovery fixed before lambda/chi despite adaptive C2",
                "acceptance to recovered canonical C1 coefficients",
                "selected semantic/copy residuals imply checked decoder success"
            ]
        },
        "wire_sections_bytes": inherited["wire_sections_bytes"],
        "maximum_body_bytes": inherited["maximum_body_bytes"],
        "new_verifier_operations": 0,
        "operation_delta_scope": "this continuation only; inherited row/image costs remain",
        "new_transmitted_values": 0,
        "measured_relation_fixture_max_bytes": 40022,
        "unapproved_controls_bytes": inherited["unapproved_controls_bytes"],
        "measurements": {
            "full_prover_time": None, "full_prover_peak_RSS": None,
            "full_transaction_CU": None, "search_time": None,
            "host_measurements": "radius-evidence.json"
        },
        "privacy": "full adaptive view simulation remains separate; no new verifier grammar",
        "grinding_security_credit_bits": 0,
        "quantum_claim": None
    }


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    data = results()
    if args.check:
        assert data == json.loads((ROOT / "radius-results.json").read_text())
        print("PASS exact boundary rational/product cross-check and committed ledger")
    else:
        print(json.dumps(data, indent=2))
