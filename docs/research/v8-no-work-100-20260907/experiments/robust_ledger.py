#!/usr/bin/env python3
"""Exact NEW robust-class ledger; all unsupported global terms stay symbolic."""
from fractions import Fraction as F
from math import comb,log2
import json
K=(2**31-1)**4;T=2**18;q=22;target=F(1,2**100)
def rec(v):return {'numerator':str(v.numerator),'denominator':str(v.denominator),'bits_display_only':log2(v.denominator)-log2(v.numerator)}
def terms(b):
    query=F(comb(min(T,b+255),q),comb(T,q))
    return query+F(q+2,K-1)+F(24,K),query+F(q,K-1)+F(18,K),query
rows=[]
for name,b in [('exact',0),('high_J_corruption_cap',9301),('original_common_zero_anchor',T-9557),('paired_common_zero_anchor',T-9556)]:
    bad,off,query=terms(b)
    rows.append(dict(name=name,B=b,matching_cap=min(T,b+255),bad_anchor=rec(bad),off_anchor_final=rec(off),query=rec(query),
        covers_whole_payment_acceptance=False,
        notes=('high-J zero anchor: SAME-final/good-boundary branch remains' if b==9301 else
               'Only bad-anchor or different-final class; no witness extraction conclusion')))
lo=0;hi=T-255
while lo<hi:
    mid=(lo+hi+1)//2
    if terms(mid)[0]<=target:lo=mid
    else:hi=mid-1
bad,off,_=terms(9301)
assert bad>off
assert terms(lo)[0]<=target<terms(lo+1)[0]
out=dict(status='formal robust causal-game bound; global source/extraction/FS applicability incomplete',rows=rows,
    largest_B_with_local_budget_only=lo,threshold_pass=rec(terms(lo)[0]),threshold_next_fail=rec(terms(lo+1)[0]),
    near_class_residual_allowance=rec(target-bad),near_class_budget_fraction_display=float(bad/target),
    raw_condition='U_no_anchor + U_good_anchor_same_final_unextracted + E_source + E_auth + E_replay + E_semantic <= 2^-100 - epsilon_near',
    FS_lift=None, FS_note='Separate resource-dependent compiler required; NOT assumed to be an additive E_FS correction',
    global_remaining_numeric_allowance=None,
    supported_allowance_explanation='target-epsilon_near is a ceiling before all symbolic terms, NOT a finished global residual budget',
    overlap='Use max(epsilon_bad_anchor,epsilon_off_final) across disjoint pre-tau bad/good anchor classes; do not add exact image error separately; four relation repairs charged once',
    canonical_body=dict(fixed=697*16,roots=52,nonces=24,records=22*621,max_frontiers=2*296*26,total=40282),
    source_callback=dict(public_dense_weight_binding_bytes=16384,complete_transaction_cu=None,production=False),
    controls=[dict(name='QM31 q23',bytes=41527,over_allowance=1245,approved=False),dict(name='quintic q22',bytes=42984,over_allowance=2702,approved=False)])
print(json.dumps(out,indent=2))
