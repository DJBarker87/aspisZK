#!/usr/bin/env python3
"""Small exact-rational parameter check, NOT an R1 security theorem.

Several deterministic R1 caps now have focused Lean checks; source, semantic
composition, actual sampler laws and FS instantiation remain open.
Only 22 binomial factors are evaluated; no finite-field enumeration occurs.
"""
import json
import math
from fractions import Fraction
from pathlib import Path

p = 2**31 - 1
K, E, H = p**4, p**8, 2**256
ceil_div = lambda a, b: (a + b - 1) // b
query_exact = Fraction(math.comb(9557, 22), math.comb(262144, 22))
query = Fraction(257 * E, H) * query_exact
rows = {
    "semantic_conservative_max": 435200 * (Fraction(1, K) + Fraction(1, H)),
    "gamma_joint_list_and_functionals": Fraction((336869026605739 + 16800) * ceil_div(H, E - 1), H),
    "kappa_joint_list_pairing": Fraction(600 * ceil_div(H, E), H),
    "alpha0_matched_and_round": Fraction((9396508281246 + 600) * ceil_div(H, E), H),
    "alpha1_repeated_lift_and_round": Fraction((9396508281246 + 600) * ceil_div(H, E), H),
    "query22_existing_envelope": query,
    "rho_subfield_residual": Fraction(21 * ceil_div(H, K), H),
}
assert all(0 < x < Fraction(1, 2**100) for x in rows.values())
assert max(rows.values()) == query

def describe(x):
    return {"numerator": str(x.numerator), "denominator": str(x.denominator),
            "negative_log2_approx": math.log2(x.denominator) - math.log2(x.numerator)}

out = {
    "status": "R1_arithmetic_ledger_deterministic_caps_checked_not_protocol_instantiated",
    "field_p": p, "query_count": 22,
    "no_work_or_grinding_credit": True,
    "rows": {k: describe(v) for k, v in rows.items()},
    "max_row": "query22_existing_envelope",
    "intended_fs_bound": "Qtot * max_row + separately justified hash/oracle collision term",
    "checked_deterministic_steps": {
        "two_concrete_folds_and_literal_joint_list": "lean/TwoFoldExtraction.lean",
        "joint_functionals_and_round_comparisons": "lean/ConcreteBinding.lean",
        "false_claims_matching_support_cap": "lean/MatchingSupport.lean",
        "subfield_residual_and_query_containment": "lean/QueryResidualBridge.lean",
    },
    "query22_exact_independent_answer_model": describe(query_exact),
    "query22_model_note": "The bounded formal sampler's successful-event mass is at most the exact ratio; exhaustion contributes zero. The retained legacy envelope is conservative, not a necessary query-sampler bias factor.",
    "open_obligations": ["actual semantic functional identification and relation composition",
                         "source correspondence including checkpoint and commitments",
                         "R1 sampler and shared-oracle FS row instantiation",
                         "privacy simulator and ROM reduction"],
    "privacy_gamma_in_subfield_event_only": describe(Fraction((K-1)*ceil_div(H,E-1), H)),
}
path = Path(__file__).with_name("security-ledger.json")
path.write_text(json.dumps(out, indent=2) + "\n")
for name, value in rows.items():
    print(f"{name}: {describe(value)['negative_log2_approx']:.9f} bits")
print("Arithmetic maximum is q22; protocol premises remain open.")
