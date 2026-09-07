#!/usr/bin/env python3
"""Exact research checks for a query-support repair of the cffcc740 example.

Not a Lean proof, adaptive extractor, actual transcript replay, or forgery.
All pass/fail tests use integers or Fraction. Float logarithms are display only.
No external dependencies. Uniform alpha includes zero, unlike the nonzero-alpha
version of the fixed-target lemma in the reviewed report.
"""
from fractions import Fraction
from itertools import combinations
from math import comb, log2
import json

P = 2**31 - 1
K = P**4
T, J, Q, DEG = 2**18, 9557, 22, 28


def choose(n, q):
    return comb(n, q) if 0 <= q <= n else 0


def entry(f):
    return {"numerator": str(f.numerator), "denominator": str(f.denominator),
            "bits_display_only": -log2(f) if f else None}


def inv(x, p):
    if x % p == 0:
        raise ValueError("Zero denominator")
    return pow(x, -1, p)


def circle_fibres(p):
    """Representatives of sign orbits; x,y nonzero and x^2+y^2=1."""
    seen, out = set(), []
    for x in range(1, p):
        for y in range(1, p):
            if (x*x + y*y - 1) % p:
                continue
            key = min(((x,y), (x,-y%p), (-x%p,-y%p), (-x%p,y)))
            if key not in seen:
                seen.add(key)
                out.append(key)
    assert len({x*x % p for x,y in out}) == len(out)
    return out


def chord(s, t, p):
    x,y = s; u,v = t
    return ((x*v-y*u)%p, (y-v)%p, (u-x)%p)


def fold(v, x, y, alpha, p):
    h, ix, iy = inv(2,p), inv(2*x%p,p), inv(2*y%p,p)
    pos = ((v[0]+v[1])*h + alpha*(v[0]-v[1])*iy) % p
    neg = ((v[2]+v[3])*h - alpha*(v[2]-v[3])*iy) % p
    return ((pos+neg)*h + alpha*alpha*(pos-neg)*ix) % p


def reciprocal_fold(a,b,c,x,y,alpha,p):
    v = [inv((a+b*xx+c*yy)%p,p)
         for xx,yy in [(x,y),(x,-y),(-x,-y),(-x,y)]]
    literal = fold(v,x,y,alpha,p)
    # After clearing the nonzero denominator, numerator is U(alpha)+x^2 V(alpha).
    u = (a*(a*a-c*c) - c*(a*a-c*c)*alpha
         - b*(a*a+c*c)*alpha**2 + 2*a*b*c*alpha**3) % p
    vv = (a*(c*c-b*b) - c*(b*b+c*c)*alpha
          + b*(b*b+c*c)*alpha**2) % p
    den = (((a+b*x)**2-c*c*y*y)*((a-b*x)**2-c*c*y*y)) % p
    reconstructed = (u + x*x*vv) * inv(den,p) % p
    assert literal == reconstructed
    return literal, vv


def toy_tests():
    fields = [17, 29, 43, 59]
    report = []
    fibre_fold_checks = gamma_alpha_checks = schedule_checks = 0
    for p in fields:
        points = circle_fibres(p)[:8]
        total = len(points)
        common = min(2, total-1)
        d = 2
        assert d*(total-common) < p
        endpoints = [(1,0), (p-1,0), (0,1), (0,p-1)]
        for s,t in combinations(endpoints,2):
            a,b,c = chord(s,t,p)
            assert (b*b+c*c)%p != 0
            residual = []
            for gamma in range(1,p):
                vals = [0]*common
                for f in range(total-common):
                    vals.append((gamma-(d*f+1))*(gamma-(d*f+2)) % p)
                assert sum(z==0 for z in vals) <= common+1
                residual.append(vals)
            coeffs = []
            exceptional = 0
            for alpha in range(p):
                fs = [reciprocal_fold(a,b,c,x,y,alpha,p) for x,y in points]
                fibre_fold_checks += total
                vv = fs[0][1]
                assert all(v == vv for _,v in fs)
                if vv == 0:
                    exceptional += 1
                else:
                    assert sum(v==0 for v,_ in fs) <= 1
                coeffs.append([f for f,_ in fs])
            assert exceptional <= 2
            for q in range(1,min(4,total)+1):
                schedules = list(combinations(range(total),q))
                allpass = badpass = 0
                for gammaidx in range(p-1):
                    for alpha in range(p):
                        zset = {i for i in range(total)
                                if residual[gammaidx][i]*coeffs[alpha][i] % p == 0}
                        good_count = choose(len(zset),q)
                        # J common fibres always pass. Every other accepting schedule
                        # fails to recover the zero components at all queried fibres.
                        allpass += good_count
                        badpass += good_count-choose(common,q)
                        gamma_alpha_checks += 1
                bad_schedules = 0
                root_count_cap = d*p + (p-1-d)*3
                for schedule in schedules:
                    if all(i<common for i in schedule):
                        continue
                    bad_schedules += 1
                    chosen = next(i for i in schedule if i>=common)
                    zeros_chosen = sum(
                        residual[gi][chosen]*coeffs[al][chosen] % p == 0
                        for gi in range(p-1) for al in range(p))
                    assert zeros_chosen <= root_count_cap
                    schedule_checks += 1
                denom = (p-1)*p*len(schedules)
                base = Fraction(choose(common,q),len(schedules))
                err = Fraction(d,p-1) + (1-Fraction(d,p-1))*Fraction(3,p)
                assert Fraction(badpass,denom) <= (1-base)*err
                assert Fraction(allpass,denom) <= base+(1-base)*err
                assert bad_schedules == len(schedules)-choose(common,q)
                report.append({"prime":p,"fibres":total,"common":common,"queries":q,
                               "chord": [a,b,c],"query_bad_support":entry(Fraction(badpass,denom)),
                               "query_bad_support_upper":entry((1-base)*err)})
    return {"small_field_profiles":len(report),"literal_reciprocal_fold_checks":fibre_fold_checks,
            "gamma_alpha_profile_checks":gamma_alpha_checks,
            "per_bad_schedule_root_checks":schedule_checks,
            "examples": report[:8]}


def main():
    base = Fraction(comb(J,Q),comb(T,Q))
    e = Fraction(DEG,K-1)+(1-Fraction(DEG,K-1))*Fraction(3,K)
    bad = (1-base)*e
    folded = base+bad
    batched = folded+Fraction(Q-1,K-1)
    # No semantic/FS/primitive terms have been granted applicability here.
    semantic = Fraction(396430,K-1)
    conditional_screen = batched+semantic
    r = Fraction(DEG*(T-J),K-1)
    assert DEG*(T-J) == 7072436
    assert bad < Fraction(1,2**119)
    assert folded < Fraction(1,2**105)
    assert batched < Fraction(1,2**105)
    sparse_bound = Fraction(2,K)+(1-Fraction(2,K))*Fraction(comb(J+2,Q),comb(T,Q))
    assert sparse_bound < Fraction(1,2**105)
    result = {
        "status":"exact arithmetic and finite tests only; no kernel-checked new theorem",
        "snapshot":"cffcc740716f220435bd9a5da05b8fc349c8d3e7",
        "challenge_law":"gamma uniform nonzero QM31; alpha uniform QM31 including zero; independent direct uniform q-subset",
        "fixed_final":"identically zero final256; the original disjoint-root/full-fibre malicious oracle construction",
        "counterexample_same_support_recovery_lower_bound":entry(r),
        "all_queries_in_common_fibres":entry(base),
        "fixed_bad_fibre_gamma_fold_upper":entry(e),
        "zero_final_query_accept_and_bad_queried_support_upper":entry(bad),
        "zero_final_all_pointwise_folded_checks_upper":entry(folded),
        "with_optional_fresh_nonzero_rho_query_batch_upper":entry(batched),
        "hypothetical_plus_semantic_screen_NOT_full_protocol":entry(conditional_screen),
        "independent_sparse_inverse_chord_counterexample_only_upper":entry(sparse_bound),
        "tests":toy_tests(),
        "limitations":["No adaptive family coverage", "No proof of the complete extractor",
                       "No bound against prover-selected future targets or challenges",
                       "No compiled Lean proof", "No source/Fiat-Shamir/AoK/privacy/CU certificate",
                       "Toy prime fields test the algebraic lemma, not the deployed QM31 sampler"]
    }
    print(json.dumps(result,indent=2))

if __name__ == '__main__':
    main()
