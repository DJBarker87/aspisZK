#!/usr/bin/env python3
"""Exact combinatorial screens; no theorem applicability inferred from arithmetic.
Outputs JSON to stdout. --test independently exhausts small binary trees.
Large arithmetic/elimination is deliberately absent; DP uses only small q.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
from math import comb, log2, isqrt
import json

P = 2**31-1

def rational(x):
    return dict(numerator=str(x.numerator), denominator=str(x.denominator),
                approximate_bits=log2(x.denominator)-log2(x.numerator) if x else None)

def maximum(d, q):
    h = (q-1).bit_length()
    return q*(d-h)+(1<<h)-q

def frontier(xs, d):
    xs=set(xs); result=0
    for _ in range(d):
        result += sum((x^1) not in xs for x in xs)
        xs={x//2 for x in xs}
    return result

@lru_cache(None)
def distribution(d,q):
    if q==0: return {0:1}
    if q>1<<d: return {}
    if d==0: return {0:1}
    out=Counter()
    for left in range(max(0,q-(1<<(d-1))),min(q,1<<(d-1))+1):
        right=q-left
        extra=int(left==0 or right==0)
        for a,na in distribution(d-1,left).items():
            for b,nb in distribution(d-1,right).items():
                out[a+b+extra]+=na*nb
    return dict(out)

def query(n,a,q):
    return F(comb(a,q),comb(n,q))

def tests():
    for d in range(1,5):
        for q in range(1,min(5,1<<d)+1):
            xs=list(combinations(range(1<<d),q))
            actual=Counter(frontier(s,d) for s in xs)
            assert distribution(d,q)==actual
            assert max(actual)==maximum(d,q)
            for a in range(q,1<<d):
                direct=F(sum(all(x<a for x in s) for s in xs),len(xs))
                assert direct==query(1<<d,a,q)
    assert 641*16+52+24+16*621+2*203*26==30824
    for q in range(1,24):
        product=F(1)
        for i in range(q): product*=F(9557-i,(1<<18)-i)
        assert product==query(1<<18,9557,q)

def row(name,d,q,a,cap,fixed,record,dense,flags):
    counts=distribution(d,q)
    assert sum(counts.values())==comb(1<<d,q)
    alpha=F(sum(v for k,v in counts.items() if k<=cap),comb(1<<d,q))
    eps=query(1<<d,a,q)
    body=fixed+52+q*record+2*cap*26
    return dict(name=name,postfold_log=d,q=q,agreement_bad_cap=a,frontier_cap=cap,
                frontier_max=maximum(d,q),body_bytes=body,delta_vs_selected=body-30824,
                delta_vs_40000=body-40000,byte_category='40000' if body<=40000 else '40960_only' if body<=40960 else 'over_40960',
                fixed_including_nonce_bytes=fixed,query_record_bytes=record,
                uniform_query=rational(eps),alpha=rational(alpha),
                conditioned_query_upper=rational(eps/alpha) if alpha else None,
                sampler64_failure=dict(base=rational(1-alpha),power=64,approximate_probability=float(1-alpha)**64),
                expected_scan64_expression='(1-(1-alpha)^64)/alpha',
                expected_scan64_approx=(1-float(1-alpha)**64)/float(alpha) if alpha else None,
                dense_bytes=dense,cu=None,prover_seconds=None,peak_rss=None,
                flags=flags,full_100_bit_claim=False)

def main():
    parser=argparse.ArgumentParser(); parser.add_argument('--test',action='store_true')
    parser.add_argument('--max-q',type=int,default=23); args=parser.parse_args()
    tests()
    if args.test: print('exact small-tree, binomial/product and baseline tests passed'); return
    rows=[]
    rows.append(row('selected-v7',18,16,9557,203,641*16+24,621,152*(1<<20),['arithmetic verified','source selected','raw security misses']))
    for q in range(16,args.max_q+1):
        rows.append(row(f'qm31-direct-q{q}',18,q,9557,maximum(18,q),641*16+24,621,152*(1<<20),['arithmetic verified','query-only change does not fix gamma/fold']))
        rows.append(row(f'two-component-ood-q{q}-canonical',18,q,9557,maximum(18,q),697*16+24,621,152*(1<<20),['arithmetic verified','pre-gamma tuple binding unresolved','adaptive hiding unresolved','SBF unmeasured']))
    # A=17066 supplied as a hypothesis, NOT inferred or certified by multiplicity=12.
    for d,q,cap in [(20,18,265),(21,17,278),(22,16,288)]:
        a=isqrt(25**2*256*(1<<d)//24**2)
        rows.append(row(f'mixed-p8-chat-crosscheck-log{d}',d,q,a,cap,355*16+286*32,683,168*(1<<(d+2)),['arithmetic verified','A=floor((25/24)*sqrt(256*N)); theorem applicability unresolved','nonce/certificate excluded per chat formula','hiding and descent unresolved']))
        # New hypothesis: hard 40,000 B, explicitly reserve the three old nonces.
        # Not a repeated old 40-KiB screen. No extra selection certificate assumed.
        fixed=355*16+286*32+24
        hardcap=(40000-fixed-52-q*683)//52
        rows.append(row(f'mixed-p8-hard40000-log{d}',d,q,a,hardcap,fixed,683,168*(1<<(d+2)),['arithmetic verified','enforced scan required','A theorem unresolved','wide D and full-view hiding unresolved','no sampler-certificate bytes reserved beyond old nonces']))
    for q in (21,22,23):
        rows.append(row(f'full-quintic-q{q}-canonical',18,q,9557,maximum(18,q),641*20+24,668,164*(1<<20),['arithmetic verified','field tested separately','theorem port unresolved','byte miss']))
    raw={
        'gamma':rational(F(336869026605739,P**4-1)),
        'fold':rational(F(9396508281246,P**4)),
        'improved_published_outer_gamma':rational(F(87316067086790,P**4-1)),
        'improved_published_outer_fold':rational(F(2388155905379,P**4)),
        'gamma_p5_same_numerator_unproved_port':rational(F(336869026605739,P**5-1)),
        'fold_p5_same_numerator_unproved_port':rational(F(9396508281246,P**5)),
        'gamma_p8_same_numerator_unproved_port':rational(F(336869026605739,P**8-1)),
        'fold_p8_same_numerator_unproved_port':rational(F(9396508281246,P**8)),
        'k14_plus_restored_k15_operational':rational(F(2*336869026605739+396430,P**4-1)),
        'v7_known_terms_subtotal_not_full_theorem':rational(F(2*336869026605739+396430,P**4-1)+F(9396508281246,P**4)+query(1<<18,9557,16)/F(sum(v for k,v in distribution(18,16).items() if k<=203),comb(1<<18,16))),
    }
    resource=[]
    for qlog in (20,36,40,48,54):
        Q=1<<qlog; R=259; M=(R+1)*(Q+1511); fresh=M+2*R; G=Q+1511+R*(2*Q+1511)
        resource.append(dict(Q=str(Q),R=R,F=str(fresh),G=str(G),
            compiler=rational(F(fresh+comb(fresh,2)+fresh*G,2**256)),
            ideal208_birthday_diagnostic=rational(F(comb(G,2),2**208)),
            status='conditional V7 compiler arithmetic; birthday diagnostic is not K1.2 theorem'))
    screen=[]
    for d in (18,20,22):
        for dim in (128,256):
            for multiplicity in (3,12):
                a=isqrt((2*multiplicity+1)**2*dim*(1<<d)//(2*multiplicity)**2)
                q=1
                while query(1<<d,a,q)>F(1,2**110): q+=1
                for extension in (4,5,8):
                    fixed_values=641-256+dim
                    record=403+(4*extension*3*31+7)//8+32
                    wire=fixed_values*4*extension+24+52+q*record+52*maximum(d,q)
                    screen.append(dict(postfold_log=d,dimension=dim,multiplicity=multiplicity,field_degree=extension,
                        rate=dict(numerator=dim,denominator=1<<d),A=a,queries_for_110_fixed_bad_set=q,
                        max_body_model=wire,query_error=rational(query(1<<d,a,q)),
                        applicability='unresolved: dimensional/fold/decoder/field/hiding port required; query screen only'))
    print(json.dumps(dict(baseline_revision='4c91f97ac6576201f90d41c2a575e54c026e3796',tests='passed',
        raw_components=raw,resources=resource,candidates=rows,bounded_parameter_screen=screen),indent=2))

if __name__=='__main__': main()
