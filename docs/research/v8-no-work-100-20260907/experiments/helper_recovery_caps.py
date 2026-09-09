#!/usr/bin/env python3
"""Exact, deliberately conditional controls for the three-helper audit.

No finite-field search, Monte Carlo, grinding credit or security certificate.
Only the existing cap formulas, finite-support accounting and binomial counts
are evaluated. Decimal bit displays are not used to discharge inequalities.
"""
import json
from decimal import Decimal, localcontext
from fractions import Fraction
from math import comb


def bits(value):
    with localcontext() as ctx:
        ctx.prec = 90
        return str(-(Decimal(value.numerator) / Decimal(value.denominator)).ln()
                   / Decimal(2).ln())


def record(value, status):
    return {"numerator": str(value.numerator), "denominator": str(value.denominator),
            "bits_display": bits(value), "status": status}


def ceiling(value):
    return -(-value.numerator // value.denominator)


def published_cap(curve_degree):
    return Fraction(112) * (Fraction(2 * 112**4, 3 * 1024) + 1) * curve_degree * 1048576


def outer_cap(n, maximum_degree, curve_degree, y_rows, z_bound):
    return (z_bound + 224*y_rows*z_bound
            + 58*(maximum_degree+1)*y_rows**2*z_bound
            + (curve_degree*n+1)*y_rows)


def monomial_count(maximum_degree, curve_degree, x_bound, y_rows, z_bound):
    return sum(max(x_bound-maximum_degree*j, 0) * max(z_bound-curve_degree*j, 0)
               for j in range(y_rows))


def main():
    k = (2**31-1)**4
    total, queries, c1_excluded = 262144, 22, 16535
    old_gamma, old_fold = 336869026605739, 9396508281246
    assert published_cap(28) == Fraction(1010607079817216, 3)
    assert ceiling(published_cap(28)) == old_gamma
    helper_cap = ceiling(published_cap(2))
    assert helper_cap == 24062073328982
    existing_initial_outer = outer_cap(1048576, 1024, 28, 112, 117078)
    existing_final_outer = outer_cap(262144, 255, 3, 113, 12594)
    assert existing_initial_outer < old_gamma
    assert existing_final_outer < old_fold
    # ONE specified lower-degree port control, not a sweep or an instantiated theorem.
    helper_z = ceiling(Fraction(117078, 14))
    helper_monomials = monomial_count(1024, 2, 114688, 112, helper_z)
    helper_constraints = 6*1048576*helper_z
    assert helper_monomials > helper_constraints
    helper_outer = outer_cap(1048576, 1024, 2, 112, helper_z)
    bad_queries = Fraction(comb(c1_excluded, queries), comb(total, queries))
    assert bad_queries > Fraction(1, 2**100)
    assert 26095 - c1_excluded - 2 == 9558
    assert 4*9558 == 38232 > 38229
    assert 245609 - (total-26095) - 2 == 9558
    # Code-geometry diagnostic: the entire old fold support may be excluded.
    assert 9558 <= c1_excluded
    payload = {
        "research_pin": "503332fbe747db381fc8ee67c4bbdd3631ec97cf",
        "k": str(k), "q": queries, "T": total,
        "existing_release_gamma": record(Fraction(old_gamma, k-1),
            "existing code-level bound; not a V8 acceptance bound"),
        "existing_release_fold": record(Fraction(old_fold, k),
            "existing degree-three code-level bound; V8 source/event adaptation separate"),
        "hypothetical_degree2_release_formula": record(Fraction(helper_cap, k-1),
            "arithmetic verified; lower-degree theorem port not implemented"),
        "hypothetical_degree2_plus_old_fold": record(Fraction(helper_cap, k-1)+Fraction(old_fold,k),
            "conditional arithmetic subtotal, not an applicable composed security ledger"),
        "existing_inner_initial_threshold": existing_initial_outer,
        "existing_inner_final_threshold": existing_final_outer,
        "one_degree2_inner_port_control": {
            "z_bound": helper_z, "monomial_count": helper_monomials,
            "constraint_count": helper_constraints, "outer_threshold": helper_outer,
            "raw_gamma": record(Fraction(helper_outer,k-1),
                "arithmetic/dimension count verified; branch/exact-message port unresolved"),
            "with_existing_inner_fold": record(Fraction(helper_outer,k-1)+Fraction(existing_final_outer,k),
                "unproved port/composition control, not achieved security")},
        "all_queries_in_fixed_c1_excluded_support": record(bad_queries,
            "exact uniform distinct-subset event at size16535; neither acceptance nor extraction failure"),
        "support_transfer": {"c1_excluded_cap": c1_excluded, "poles_cap":2,
            "required_quotient_matching":26095, "retained_fibres":9558,
            "retained_symbols":38232, "old_initial_strict_floor":38229,
            "old_fold_support_may_all_be_excluded":True}}
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
