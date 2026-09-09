#!/usr/bin/env python3
"""Tiny exact F17 control, not a production-field probability experiment.

Enumerates all 17 alpha values and all 17 constant-code final messages for
ONE fixed received word. The two disjoint circle fibres have distinct final
points. This tests the proposed global-fold statement, not partial agreement,
arbitrary pre-OOD commitment strategies, or payment acceptance.
"""
import json

P = 17
POINTS = ((3, 3), (6, 4))
COEFF = (11, 11, 11, 1)  # (alpha-1)(alpha-2)(alpha-3)


def inv(x):
    assert x % P
    return pow(x, -1, P)


def evaluate(x, y, coefficients):
    a, b, c, d = coefficients
    return tuple((a + yy*b + xx*c + xx*yy*d) % P
                 for xx, yy in ((x, y), (x, -y), (-x, -y), (-x, y)))


def fold(values, alpha, x, y):
    a, b, c, d = values
    pos = ((a+b)*inv(2) + alpha*(a-b)*inv(2*y)) % P
    neg = ((c+d)*inv(2) - alpha*(c-d)*inv(2*y)) % P
    return ((pos+neg)*inv(2) + alpha*alpha*(pos-neg)*inv(2*x)) % P


def decode(values, x, y):
    a, b, c, d = values
    return ((a+b+c+d)*inv(4) % P,
            (a-b-c+d)*inv(4*y) % P,
            (a+b-c-d)*inv(4*x) % P,
            (a-b+c-d)*inv(4*x*y) % P)


def main():
    fibres = [{(xx % P, yy % P) for xx, yy in
               ((x, y), (x, -y), (-x, -y), (-x, y))} for x, y in POINTS]
    assert all((x*x+y*y) % P == 1 and x*y % P for x, y in POINTS)
    assert all(len(f) == 4 for f in fibres)
    assert fibres[0].isdisjoint(fibres[1])
    assert len({(2*x*x-1) % P for x, _ in POINTS}) == 2
    received = ((0, 0, 0, 0), evaluate(*POINTS[1], COEFF))
    exact_alphas = []
    for alpha in range(P):
        actual = tuple(fold(v, alpha, *point) for v, point in zip(received, POINTS))
        cubic = ((alpha-1)*(alpha-2)*(alpha-3)) % P
        assert actual == (0, cubic)
        # Every final message in this constant code is considered after alpha.
        matching = [c for c in range(P) if (c, c) == actual]
        if matching:
            assert matching == [0]
            exact_alphas.append(alpha)
    assert exact_alphas == [1, 2, 3]
    # A lift of the constant final code has the same four coefficients on
    # both fibres. The all-zero first fibre forces those coefficients zero,
    # but the second received fibre has a nonzero decoded coefficient vector.
    # Check the two 4x4 linear inverses on all coordinate basis vectors.
    for point in POINTS:
        for j in range(4):
            basis = tuple(int(i == j) for i in range(4))
            assert decode(evaluate(*point, basis), *point) == basis
    assert decode(received[0], *POINTS[0]) == (0, 0, 0, 0)
    assert decode(received[1], *POINTS[1]) == COEFF
    print(json.dumps({
        "field": P,
        "points": POINTS,
        "received": received,
        "exact_adaptive_final_alphas": exact_alphas,
        "all_alpha_final_pairs_checked": P*P,
        "local_inverse_basis_vectors_checked": 8,
        "scope": "one fixed pre-alpha quotient word; globally exact constant-code finals",
        "claim": "three-value bound is attained; no partial-agreement or payment claim",
    }, sort_keys=True))


if __name__ == "__main__":
    main()
