#!/usr/bin/env python3
"""Exact companion to FixedTargetQuerySupport.lean; NOT adaptive security.

No witnesses, network calls, file writes, or probabilistic security estimates.
The supplied package is retained verbatim apart from trailing whitespace.
--replay-package reruns its already-reviewed finite tests, only when needed.
"""
import argparse
from fractions import Fraction
import hashlib
from itertools import product
import json
from math import log2
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
PACKAGE = HERE / "lean-repair-package"


def ratio_entry(value):
    return {"numerator": str(value.numerator),
            "denominator": str(value.denominator),
            "bits_display_only": -log2(value) if value else None}


def query_ratio(common, total, queries):
    """Independent falling-product calculation, not math.comb from the ZIP."""
    if queries > total or queries < 0:
        raise ValueError("Empty sampling space")
    if queries > common:
        return Fraction(0)
    out = Fraction(1)
    for i in range(queries):
        out *= Fraction(common - i, total - i)
    return out


def small_normalization_tests():
    count = 0
    for g, a, total in product(range(1, 7), repeat=3):
        for d, t, common in product(range(g+1), range(a+1), range(total+1)):
            lhs = Fraction((total-common)*(d*a+(g-d)*t), total*g*a)
            rhs = (1-Fraction(common, total)) * (
                Fraction(d, g)+(1-Fraction(d, g))*Fraction(t, a))
            assert lhs == rhs
            count += 1
    return count


def relaxed_cover_countermodel():
    """Constant-code toy: a relaxed close-list still need not cover acceptance.

    Different hypothesis from the previous floor-two toy: each exceptional
    gamma now creates TWO matching fibres, while the close-list floor is three.
    This is not a QM31/circle-code counterexample or a payment attack.
    """
    prime = 17
    words = [(0, 0, 0)] * 2
    for group in range(3):
        left, right = 2*group+1, 2*group+2
        coeff = (left*right % prime, -(left+right) % prime, 1)
        words.extend([coeff, coeff])
    family = []
    maximum_joint_agreement = 0
    for target in product(range(prime), repeat=3):
        matches = sum(word == target for word in words)
        maximum_joint_agreement = max(maximum_joint_agreement, matches)
        if matches >= 3:
            family.append(target)
    assert maximum_joint_agreement == 2 and family == []
    high_agreement_gammas = []
    accepted_pairs = 0
    from math import comb
    for gamma in range(1, prime):
        matches = sum((a+b*gamma+c*gamma*gamma) % prime == 0 for a, b, c in words)
        if matches >= 4:
            high_agreement_gammas.append(gamma)
        accepted_pairs += comb(matches, 3)
    assert high_agreement_gammas == list(range(1, 7))
    probability = Fraction(accepted_pairs, (prime-1)*comb(8, 3))
    assert probability == Fraction(3, 112)
    return {"evidence": "small exhaustive countermodel, not the actual circle code",
            "constant_component_tuples_enumerated": prime**3,
            "fibres": 8, "common": 2, "relaxed_joint_list_floor": 3,
            "combined_agreement_threshold": 4, "joint_family_size": len(family),
            "high_agreement_gammas": high_agreement_gammas,
            "queries": 3, "accepted_zero_query_probability": ratio_entry(probability),
            "conclusion": "A low-cardinality close family alone does not cover every accepted discarded branch; a separate joint bad-event bound is necessary."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--test", action="store_true")
    parser.add_argument("--replay-package", action="store_true")
    args = parser.parse_args()
    archived = json.loads((PACKAGE / "results.json").read_text())
    replay = None
    if args.replay_package:
        result = json.loads(subprocess.check_output(
            [sys.executable, str(PACKAGE / "check_query_support.py")]))
        assert result == archived
        replay = {k: v for k, v in result["tests"].items() if k != "examples"}
    p = 2**31-1
    k = p**4
    j, total, q, d = 9557, 2**18, 22, 28
    base = query_ratio(j, total, q)
    # Exact numerator proved by two_stage_count; gamma nonzero, alpha whole K.
    cap = d*k+(k-1-d)*3
    error = Fraction(cap, (k-1)*k)
    assert error == Fraction(d, k-1)+(1-Fraction(d, k-1))*Fraction(3, k)
    wrong = (1-base)*error
    pointwise = base+wrong
    package_batch = pointwise+Fraction(q-1, k-1)
    source_shaped_batch = pointwise+Fraction(q, k-1)
    for key, value in [
        ("all_queries_in_common_fibres", base),
        ("fixed_bad_fibre_gamma_fold_upper", error),
        ("zero_final_query_accept_and_bad_queried_support_upper", wrong),
        ("zero_final_all_pointwise_folded_checks_upper", pointwise),
        ("with_optional_fresh_nonzero_rho_query_batch_upper", package_batch),
    ]:
        supplied = archived[key]
        assert value == Fraction(int(supplied["numerator"]), int(supplied["denominator"]))
    assert wrong < Fraction(1, 2**119)
    assert source_shaped_batch < Fraction(1, 2**105)
    # Later alpha repairs, acceptance bridge, adaptive coverage, FS and
    # primitives are deliberately not zero-filled into this fixed-target screen.
    result = {
        "evidence": "exact arithmetic verified; generic finite counting kernel-checked separately",
        "not_a_full_protocol_bound": True,
        "parameters": {"p": p, "field_size": str(k), "fibres": total,
                       "common_fibres": j, "queries": q, "gamma_degree": d},
        "challenge_law": "independent direct uniform q-subset; gamma uniform K minus zero; alpha uniform whole K",
        "all_common": ratio_entry(base),
        "pointwise_accept_and_wrong_queried_support": ratio_entry(wrong),
        "pointwise_accept": ratio_entry(pointwise),
        "optional_unshifted_or_zero_prior_batch": ratio_entry(package_batch),
        "general_tag73_prior_plus_shifted_batch": ratio_entry(source_shaped_batch),
        "batch_correction": ratio_entry(Fraction(1, k-1)),
        "hypothetical_plus_recorded_eight_category_396430_inventory_NOT_full_theorem":
            ratio_entry(source_shaped_batch+Fraction(396430, k-1)),
        "source_batch_degree": q,
        "source_batch_polynomial": "prior - rho * sum_i residual_i * rho^i",
        "source_batch_condition": "prior and residual vector fixed before fresh nonzero rho; later relation repairs separate",
        "tests": {"normalization_cases": small_normalization_tests() if args.test else None,
                  "independent_large_rational_crosschecks": 5,
                  "package_replay": replay},
        "relaxed_cover_countermodel": relaxed_cover_countermodel(),
        "source_hashes": {f: hashlib.sha256((HERE/f).read_bytes()).hexdigest()
                          for f in ["FixedTargetQuerySupport.lean", "lean_repair_screen.py",
                                    "lean-repair-package/check_query_support.py"]},
        "open": ["adaptive accepted discarded-branch coverage", "actual final equals fixed-target fold",
                 "source sampling/nonce and FS resource transfer", "authentication and later relation repairs",
                 "full-view ZK", "matched complete-transaction CU"]
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
