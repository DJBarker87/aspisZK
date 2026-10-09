#!/usr/bin/env python3
"""Tiny exact prerequisite falsification, not a payment/verifier experiment.

Exhausts the displayed F7 residual family, three query locations and all
gamma/alpha/query outcomes. It does not search or extrapolate QM31 rates.
"""
import json
from itertools import combinations

P = 7
G = tuple(range(1, P))
A = tuple(range(P))
U = tuple(range(3))
Q = 1
SCHEDULES = tuple(combinations(U, Q))


def fold(values, alpha):
    # Exact four-sign fold at x=y=1, in the existing low-bit order.
    v0, v1, v2, v3 = values
    inv4 = pow(4, -1, P)
    coefficients = (
        (v0 + v1 + v2 + v3) * inv4,
        (v0 - v1 - v2 + v3) * inv4,
        (v0 + v1 - v2 - v3) * inv4,
        (v0 - v1 + v2 - v3) * inv4,
    )
    return sum(c * pow(alpha, i, P) for i, c in enumerate(coefficients)) % P


def pointwise(schedule, gamma, alpha, common, root, pole=False):
    for i in schedule:
        residual = 0 if i in common else (gamma - root) % P
        # Totalized field division alone maps a pole to zero; the event must
        # retain the actual check separately.
        values = [0 if pole and i not in common else residual] * 4
        if fold(values, alpha) != 0:
            return False
    return True


def count(predicate):
    return sum(predicate(s, g, a) for s in SCHEDULES for g in G for a in A)


def main():
    common = frozenset((0, 1))
    exception = frozenset((1,))
    charged = count(lambda s, g, a: g in exception and pointwise(s, g, a, common, 1))
    uncharged = count(lambda s, g, a: pointwise(s, g, a, common, 1))
    common_part = count(lambda s, g, a:
                        set(s) <= common and g in exception and pointwise(s, g, a, common, 1))
    wrong_part = charged - common_part
    wrong_cap = len(A) + (len(G) - 1) * 3
    charged_cap = 2 * len(exception) * len(A) + wrong_cap
    assert (charged, common_part, wrong_part, charged_cap) == (21, 14, 7, 36)
    assert uncharged == 91 and uncharged > charged_cap

    # A singleton chosen AFTER gamma is not one fixed exception set.
    retrospective_common = count(lambda s, g, a: set(s) <= common and g in {g})
    assert retrospective_common == 84 and retrospective_common > common_part

    # A zero denominator cannot be made safe by totalized division.
    unsafe_wrong = count(lambda s, g, a:
                         not set(s) <= common and pointwise(s, g, a, common, 1, pole=True))
    safe_pole = count(lambda s, g, a:
                      set(s) <= common and g in exception and pointwise(s, g, a, common, 1, pole=True))
    assert unsafe_wrong == 42 and unsafe_wrong > wrong_cap
    assert safe_pole == 14

    # Member choice may depend on already seen challenges. The complete
    # pointwise union is used; no selected member is frozen retroactively.
    family = ((common, 1), (frozenset((1, 2)), 2))
    adaptive_union = count(lambda s, g, a:
        any(g == root and pointwise(s, g, a, own, root) for own, root in family))
    assert adaptive_union == 42 and adaptive_union <= 2 * charged_cap
    print(json.dumps({
        "scope": "exhaustive outcomes of one fixed F7 two-tuple residual family, not all strategies",
        "outcomes_per_tuple": len(SCHEDULES) * len(G) * len(A),
        "charged_count": charged,
        "common_count": common_part,
        "wrong_count": wrong_part,
        "proved_shape_upper_bound": charged_cap,
        "without_gamma_charge_count": uncharged,
        "after_gamma_singleton_common_count": retrospective_common,
        "unchecked_zero_denominator_wrong_count": unsafe_wrong,
        "pole_rejecting_count": safe_pole,
        "adaptive_two_member_union_count": adaptive_union,
        "quantum_or_QM31_probability_claim": None,
    }, indent=2))


if __name__ == "__main__":
    main()
