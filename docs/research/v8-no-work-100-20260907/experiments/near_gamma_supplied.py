#!/usr/bin/env python3
"""Exact checks for a near-anchor gamma-cover proposal after a33f4f6b.

Only standard-library arithmetic. No network access, Lean, SBF, payment
verification, or sampling-based claim at cryptographic probabilities.
"""
from __future__ import annotations
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from math import comb, log2
import json

REV = 'a33f4f6b2a11b52680597a5f849a63fe221f3fcb'

def probability(x: Fraction) -> dict:
    assert x > 0
    return {'numerator': str(x.numerator), 'denominator': str(x.denominator),
            'bits_display_only': log2(x.denominator)-log2(x.numerator)}

def concrete() -> dict:
    p=2**31-1; k=p**4; T=2**18; B=9301; q=22
    r=29; m=64; overlap=256
    load=m*(T-B)//T
    left=T*comb(load,r); right=(B+overlap)*comb(m,r)
    assert load==61 and left>right
    common=Fraction(left,comb(m,r))
    mismatches=m*B//(m-r+1)
    assert mismatches==16535
    assert 2*(T-mismatches)-T>overlap
    query=Fraction(comb(B+255,q),comb(T,q))
    independent=Fraction(1)
    for j in range(q): independent*=Fraction(B+255-j,T-j)
    assert query==independent
    local=Fraction(q+3,k-1)+Fraction(24,k)+query
    few=Fraction(m-1,k-1)
    # A proposed composition ONLY for image-valid near anchors and point-claim
    # correctness relative to the constructed tuple, not full witness extraction.
    dense=Fraction(r-1,k-1)+local
    composed=max(few,dense)
    assert composed==dense and composed<Fraction(1,2**105)
    rows=[]
    for noise in [0,1,9301,10980,10981]:
        e=Fraction(q+3,k-1)+Fraction(24,k)+Fraction(comb(noise+255,q),comb(T,q))
        rows.append({'B':noise,'local_bound':probability(e),
                     'local_le_2_minus_100':e<=Fraction(1,2**100)})
    return {
        'revision':REV,'T':T,'B':B,'q':q,'code_overlap_cap':overlap,
        'curve_degree':r-1,'mathematical_anchor_pool':m,'interpolation_nodes':r,
        'balanced_load_floor':load,'certificate_lhs':str(left),
        'certificate_rhs':str(right),'strict_certificate_verified':True,
        'mean_common_support_lower':{'numerator':str(common.numerator),
            'denominator':str(common.denominator),'display':float(common)},
        'own_support_fibres':T-mismatches,'own_support_symbols':4*(T-mismatches),
        'local_rows':rows,'small_good_gamma_branch':probability(few),
        'proposed_near_gamma_point_binding_bound':probability(composed),
        'local_target_budget_used_percent':float(local*2**100)*100,
        'body_bytes':697*16+52+24+q*621+2*296*26,
        'fixed_one_bad_fibre_miss':{'numerator':131061,'denominator':131072},
        'global_security_bound':None,'source_refinement':False,'Lean_replay':False,
        'scope':'Generic curve-cover derivation plus exact tests. No payment witness, far-anchor, ZK, FS, source or CU claim.'}

def curve_cover_tests() -> dict:
    """All two-coefficient received curves over alphabet {0,1,2} in F5^4.
    Each curve is compared against EVERY constant codeword at EVERY nonzero
    field challenge. Candidate membership is determined, never supplied.
    """
    p=5; T=4; B=1; r=2; m=3; overlap=0
    assert T*comb(m*(T-B)//T,r)>(B+overlap)*comb(m,r)
    challenges=range(1,p)
    seen=dense=sparse=represented=own_checks=0
    for flat in product(range(3),repeat=r*T):
        words=[flat[:T],flat[T:]]
        received={g:tuple((words[0][j]+g*words[1][j])%p for j in range(T)) for g in challenges}
        candidates={g:[c for c in range(p) if sum(v==c for v in received[g])>=T-B] for g in challenges}
        good=[g for g in challenges if candidates[g]]
        seen+=1
        if len(good)<m:
            sparse+=1
            continue
        dense+=1
        pool=good[:m]
        selected={g:candidates[g][0] for g in pool}
        support={g:{j for j in range(T) if received[g][j]==selected[g]} for g in pool}
        nodes=next((pair for pair in combinations(pool,r)
                    if len(support[pair[0]]&support[pair[1]])>B+overlap),None)
        assert nodes is not None
        x,y=nodes
        c1=(selected[y]-selected[x])*pow(y-x,-1,p)%p
        c0=(selected[x]-x*c1)%p
        for g in good:
            for candidate in candidates[g]:
                assert candidate==(c0+g*c1)%p
                represented+=1
        own=sum(words[0][j]!=c0 or words[1][j]!=c1 for j in range(T))
        assert own<=m*B//(m-r+1)
        own_checks+=1
    return {'received_curves':seen,'dense_case':dense,'small_good_set_case':sparse,
            'actual_near_candidates_covered':represented,'own_support_checks':own_checks,
            'field':p,'received_alphabet':[0,1,2],
            'scope':'Exhaustive over the stated received alphabet, not all F5 words or Aspis instances.'}

def adaptive_inactive_tests() -> dict:
    """All nonzero 3x2 component-error arrays over F5. Inactive error is
    maximized independently at every gamma, but BEFORE kappa. This tests
    the timing allowed by the proposed two-level gamma/kappa reduction.
    """
    p=5; G=range(1,p); checks=nonzero_gamma_rows=worst=0
    for flat in product(range(p),repeat=6):
        if not any(flat): continue
        errors=[flat[0:2],flat[2:4],flat[4:6]]
        totals=0; joint_zero=0
        for gamma in G:
            e=[(a+gamma*b)%p for a,b in errors]
            values=[(kap*e[0]+kap*kap*e[1]+kap**3*e[2])%p for kap in G]
            # Choosing inactive=-v causes acceptance on each kappa giving v.
            maximum=max(Counter(values).values())
            brute=max(sum((inactive+v)%p==0 for v in values) for inactive in range(p))
            assert maximum==brute
            if any(e):
                assert maximum<=3
                nonzero_gamma_rows+=1
            else: joint_zero+=1
            totals+=maximum
        assert joint_zero<=1
        assert totals<=1*(p-1)+((p-1)-1)*3
        worst=max(worst,totals);checks+=1
    # Allowing inactive AFTER kappa makes any errors cancel; keep the forbidden
    # strategy as a timing regression rather than assuming it away silently.
    for gamma,kap in product(G,repeat=2):
        e0,e1,e2=1,gamma,2
        inactive=-(kap*e0+kap**2*e1+kap**3*e2)%p
        assert (inactive+kap*e0+kap**2*e1+kap**3*e2)%p==0
    return {'nonzero_component_error_arrays':checks,
            'nonzero_gamma_row_cases':nonzero_gamma_rows,
            'largest_adaptive_inactive_pair_count':worst,'gamma_kappa_pairs':(p-1)**2,
            'universal_two_stage_root_cap':13,'late_inactive_failure_cases':16,
            'scope':'Maximizes inactive error over every pre-kappa choice independently for each gamma; not full relation acceptance.'}

def high_j_regression() -> dict:
    p=17; T=24; J=20; B=T-J; degree=2; m=6
    coeff=[[0]*T for _ in range(degree+1)]
    for s in range(B):
        a=2*s+1;b=a+1
        coeff[0][J+s]=a*b%p
        coeff[1][J+s]=-(a+b)%p
        coeff[2][J+s]=1
    assert T*comb(m*(T-B)//T,degree+1)>B*comb(m,degree+1)
    represented=exceptional=0
    for gamma in range(1,p):
        received=[sum(pow(gamma,l,p)*coeff[l][i] for l in range(3))%p for i in range(T)]
        near=[c for c in range(p) if sum(v==c for v in received)>=T-B]
        assert near==[0]
        represented+=1
        supp=[i for i,v in enumerate(received) if v==0]
        if gamma<=2*B:
            assert len(supp)==J+1
            assert any(coeff[2][i]==1 for i in supp)
            exceptional+=1
    return {'field':p,'represented_near_candidates':represented,
            'exceptional_same_support_failures_retained':exceptional,
            'own_support':J,'combined_support_on_exceptions':J+1,
            'scope':'Small high-J analogue; fixed zero component curve covers candidates on its own support.'}

def main() -> None:
    print(json.dumps({'concrete':concrete(),'cover_checks':curve_cover_tests(),
          'adaptive_inactive_checks':adaptive_inactive_tests(),
          'root_product_regression':high_j_regression()},indent=2))

if __name__=='__main__':main()
