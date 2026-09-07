"""Exact joint-event arithmetic and tiny exhaustive fixed-target lemma checks.
Logs are presentation only; every pass/fail comparison uses integers/rationals.
"""
import json
from fractions import Fraction as F
from itertools import combinations, product
from math import comb, log2

P = 2**31-1
T, J, DEG, Q = 2**18, 9557, 28, 22
K = P**4
M = DEG*(T-J)
recovery = F(M, K-1)
query_base = F(comb(J,Q),comb(T,Q))
query_extra = F(comb(J+1,Q),comb(T,Q))
# Exact subevent: all queries fall in zero fibres. Other folds can cancel;
# these formulas do not claim to enumerate every passing query schedule.
zero_fibre_subevent = (1-recovery)*query_base + recovery*query_extra
assert F(1,2**102) < recovery < F(1,2**101)
assert recovery > F(2800,K-1)
assert recovery > F(1,2**104)
assert zero_fibre_subevent < F(1,2**105)

# Tiny independent exhaustive construction: p17, 8 fibres, 2 common, degree2.
small_support = []
for gamma in range(1,17):
    support = 2 + sum(((gamma-(2*s+1))*(gamma-(2*s+2))) % 17 == 0 for s in range(6))
    small_support.append(support)
assert small_support.count(3)==12 and small_support.count(2)==4
assert sum(comb(s,2) for s in small_support)==12*comb(3,2)+4*comb(2,2)

# Exhaust all root-set configurations for 3 fixed residual polynomials over F5,
# degree <=2. None represents identically zero. Every other set is realizable
# by product(T-r); the empty set uses the nonzero constant polynomial.
rootsets = [frozenset(c) for n in range(3) for c in combinations(range(5), n)] + [None]
checks = 0
for rows in product(rootsets, repeat=3):
    common = sum(r is None for r in rows)
    for queries in range(1,4):
        good = 0
        for sched in combinations(range(3),queries):
            for gamma in range(5):
                good += all(rows[i] is None or gamma in rows[i] for i in sched)
        base = F(comb(common,queries),comb(3,queries)) if common>=queries else F(0)
        assert F(good,5*comb(3,queries)) <= base + (1-base)*F(2,5)
        checks += 1

# Exact normalized four-point fold at x=y=2 on the F7 circle. All 255 nonzero
# binary coefficient patterns for four affine-in-gamma residuals are tested.
# Gamma and alpha are uniform nonzero F7, not selected by the prover.
fold_checks = 0
for coeffs in product(range(2),repeat=8):
    if not any(coeffs):
        continue
    zeros = 0
    for gamma, alpha in product(range(1,7),repeat=2):
        v = [(coeffs[i]+gamma*coeffs[i+4])%7 for i in range(4)]
        pos = ((v[0]+v[1])*4 + alpha*(v[0]-v[1])*2)%7
        neg = ((v[2]+v[3])*4 - alpha*(v[2]-v[3])*2)%7
        folded = ((pos+neg)*4 + alpha*alpha*(pos-neg)*2)%7
        zeros += folded==0
    assert F(zeros,36) <= F(1,6)+(1-F(1,6))*F(3,6)
    fold_checks += 1
fold_bad = F(DEG,K-1)+(1-F(DEG,K-1))*F(3,K-1)
q5_known = F(comb(J,21),comb(T,21)) + F(2*336869026605739+396430+3+21+18,P**5-1) + F(9396508281246,P**5)
assert q5_known < F(1,2**100)  # a conditional known-stage subtotal, NOT a full theorem

# DEEP ITCS2020 Theorem3/25 and general-linear-code Lemma28: if displayed
# threshold t dominates both 2L*epsilon^(1/3) and 4/(epsilon^2*K), then
# t^7 >= 256*L^6/K. This is an obstruction to using THAT upper-bound formula,
# not a lower bound on the protocol's true error. Even L=1 cannot give 100 bits.
deep_obstruction = F(256,K)
assert deep_obstruction > F(1,2**700)
assert K < 2**124

def entry(x):
    return {"numerator": str(x.numerator), "denominator": str(x.denominator),
            "bits_display_only": -log2(x)}

print(json.dumps({
    "status": "arithmetic verified; fixed-target lemma exhaustive small cases; full theorem unresolved",
    "field": "QM31", "fibres":T, "common_fibres":J, "extra_fibres":1,
    "degree":DEG, "queries":Q, "bad_gamma_count":M,
    "same_support_joint_recovery_lower_bound":entry(recovery),
    "query_on_extra_support":entry(query_extra),
    "rare_gamma_and_all_zero_fibres_subevent":entry(recovery*query_extra),
    "all_gamma_all_zero_fibres_subevent":entry(zero_fibre_subevent),
    "fixed_target_only_union_upper_bound":entry(query_base+(1-query_base)*F(DEG,K-1)),
    "fixed_target_folded_union_upper_bound":entry(query_base+(1-query_base)*fold_bad),
    "quintic_q21_retained_known_stage_subtotal_unproved_port":entry(q5_known),
    "deep_2020_formula_bits_ceiling_even_L1":(log2(K)-8)/7,
    "deep_2020_formula_seventh_power_lower_bound":entry(deep_obstruction),
    "exhaustive_fixed_target_checks":checks,
    "exhaustive_binary_four_point_fold_checks":fold_checks,
    "limits":["not full acceptance", "no adaptive tuple-existence lemma", "no ZK theorem",
              "no FS resource lift", "no V8 CU measurement", "DEEP formula not claimed applicable"]
},indent=2))
