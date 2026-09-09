#!/usr/bin/env python3
"""Exact small-code tests of the three-node support margin, not security rates."""
from itertools import combinations, product
import json

P = 7
G = (1, 2, 3, 4)


def ev(c, x):
    z = 0
    for a in reversed(c):
        z = (z*x+a) % P
    return z


def root_product(roots):
    c = [1]
    for r in roots:
        n = [0]*(len(c)+1)
        for i, a in enumerate(c):
            n[i] = (n[i]-r*a) % P
            n[i+1] = (n[i+1]+a) % P
        c = n
    return c


def result():
    # At the failed strict boundary T=4,B=1,delta=0, received word j is
    # X^3-product_{g != j}(X-g), so each coordinate has degree<=2.
    # Gamma g is close to constant codeword g^3, missing exactly coordinate g.
    received = []
    for j in G:
        c = root_product(g for g in G if g != j)
        q = [(-a) % P for a in c]
        q[3] = (q[3]+1) % P
        assert q[3] == 0
        received.append(tuple(q[:3]))
    targets = {g: pow(g, 3, P) for g in G}
    for j, q in zip(G, received):
        for g in G:
            assert (ev(q,g) == targets[g]) == (g != j)
    quads = list(product(range(P), repeat=3))
    fits = [q for q in quads if all(ev(q,g) == targets[g] for g in G)]
    assert fits == []
    # Independent positive check: add any fifth quadratic coordinate.
    # Then T=5>4B. Exhaust all343 fifth curves, all nonzero gamma values,
    # and ALL constant-code candidates; no assumed candidate membership.
    dense = sparse = covered_pairs = nodal_choices = 0
    for fifth in quads:
        word = received+[fifth]
        near = {g: [a for a in range(P)
                    if sum(ev(q,g) != a for q in word) <= 1]
                for g in range(1,P)}
        good = [g for g in near if near[g]]
        if len(good) < 3:
            sparse += 1
            continue
        dense += 1
        for nodes in combinations(good,3):
            assert all(len(near[g]) == 1 for g in nodes)
            candidates = [q for q in quads
                          if all(ev(q,g) == near[g][0] for g in nodes)]
            assert len(candidates) == 1
            interpolant = candidates[0]
            for g in good:
                for target in near[g]:
                    assert ev(interpolant,g) == target
                    covered_pairs += 1
            nodal_choices += 1
    assert dense > 0 and dense+sparse == 343
    # Exact selected arithmetic is only an applicability screen until the
    # actual support/code/claim game is instantiated.
    S, delta = 245609, 256
    radius = (S-delta-1)//4
    assert radius == 61338 and 4*radius+delta < S
    assert 4*(radius+1)+delta >= S
    final_radius = (radius-2)//4
    assert final_radius == 15334 and 4*final_radius+2 == radius
    return {
        'field':P,
        'scope':'exact constant-code margin falsifier and restricted received-family exhaustive positive checks; not an Aspis acceptance bound',
        'boundary':{'T':4,'B':1,'delta':0,'gamma_nodes':list(G),
                    'received_quadratics':[list(q) for q in received],
                    'targets':{str(g):a for g,a in targets.items()},
                    'quadratic_covers_of_all_four_targets':len(fits)},
        'strict_margin_checks':{'T':5,'B':1,'fifth_quadratics':343,
                                'dense_cases':dense,'sparse_cases':sparse,
                                'nodal_choices':nodal_choices,'covered_pairs':covered_pairs},
        'selected_arithmetic_only':{'fixed_C1_support_floor':S,'overlap_cap':delta,
                                    'helper_support_radius':radius,
                                    'suggested_final_radius_after_4B_plus_2':final_radius},
        'global_security_bound':None,
    }


if __name__ == '__main__':
    print(json.dumps(result(), indent=2))
