#!/usr/bin/env python3
"""Exact research checks for a specified joint image/relation gate.
Not production code, an adaptive arbitrary-oracle theorem, or a Lean replay.
Python standard library only; writes no files unless --output is supplied.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
from itertools import product, combinations
from math import comb, log2
import json
import random

P=2**31-1
K=P**4
Z=(0,0,0,0)
O=(1,0,0,0)
I=(0,1,0,0)

def sc(n): return (n%P,0,0,0)
def add(a,b): return tuple((u+v)%P for u,v in zip(a,b))
def sub(a,b): return tuple((u-v)%P for u,v in zip(a,b))
def scale(a,t): return tuple(u*t%P for u in a)
def cm(a,b):
    x,y=a; z,w=b
    return ((x*z-y*w)%P,(x*w+y*z)%P)
def mul(a,b):
    ac=cm(a[:2],b[:2]); bd=cm(a[2:],b[2:])
    cross=cm(add(a[:2],a[2:]),add(b[:2],b[2:]))
    return add(ac,cm((2,1),bd))+sub(sub(cross,ac),bd)
def power(a,n):
    out=O
    while n:
        if n&1: out=mul(out,a)
        a=mul(a,a); n//=2
    return out
def inv(a):
    if a==Z: raise ZeroDivisionError('zero field element')
    return power(a,K-2)
def div(a,b): return mul(a,inv(b))
def total(xs):
    s=Z
    for x in xs: s=add(s,x)
    return s

def circle(t):
    t2=mul(t,t); den=add(O,t2)
    return div(sub(O,t2),den),div(scale(t,2),den)

def chord(s,t):
    x,y=s; u,v=t
    return sub(mul(x,v),mul(y,u)),sub(y,v),sub(u,x)

def peval(poly,x):
    out=Z
    for c in reversed(poly): out=add(mul(out,x),c)
    return out

def cheb(n):
    """M31 coefficients for T_n, generated independently of tensor carry."""
    if n==0:return [1]
    before=[1]; now=[0,1]
    for _ in range(1,n):
        nxt=[0]*(len(now)+1)
        for j,v in enumerate(now): nxt[j+1]=2*v%P
        for j,v in enumerate(before): nxt[j]=(nxt[j]-v)%P
        before,now=now,nxt
    return now


def outside_quotient(n,s,t):
    """Laurent Q of (T_n-I)/L; quotient exponents -(n-1)..n-1."""
    a,b,c=chord(s,t)
    half=pow(2,-1,P)
    lo=scale(add(b,mul(I,c)),half)
    hi=scale(sub(b,mul(I,c)),half)
    assert lo!=Z and hi!=Z
    xs,ys=s; xt,yt=t
    f=cheb(n)
    f0=peval([sc(v) for v in f],xs)
    f1=peval([sc(v) for v in f],xt)
    h0,h1=(xs,xt) if xs!=xt else (ys,yt)
    slope=div(sub(f0,f1),sub(h0,h1))
    intercept=sub(f0,mul(slope,h0))
    if xs!=xt:
        il=ih=scale(slope,half)
    else:
        il=scale(mul(I,slope),half)
        ih=scale(mul(I,slope),-half)
    num=[Z]*(2*n+1)
    num[0]=num[2*n]=sc(half)
    num[n]=sub(num[n],intercept)
    num[n-1]=sub(num[n-1],il)
    num[n+1]=sub(num[n+1],ih)
    rem=num.copy(); q=[Z]*(2*n-1); hi_inv=inv(hi)
    for j in range(2*n,1,-1):
        v=mul(rem[j],hi_inv); q[j-2]=v
        rem[j]=Z
        rem[j-1]=sub(rem[j-1],mul(a,v))
        rem[j-2]=sub(rem[j-2],mul(lo,v))
    assert all(v==Z for v in rem)
    rebuilt=[Z]*(2*n+1)
    for j,v in enumerate(q):
        for d,l in enumerate([lo,a,hi]): rebuilt[j+d]=add(rebuilt[j+d],mul(v,l))
    assert rebuilt==num
    assert add(mul(hi,q[-1]),mul(lo,q[0]))==O
    # Leading T_(n-1) and U_(n-2) coefficients convert to the top tensor slots.
    # n is a power of two: ratio of leading monomial coefficients is n/2.
    A_top=scale(add(q[-1],q[0]),n//2)
    B_next=scale(mul(I,sub(q[-1],q[0])),n//2)
    assert sub(mul(b,A_top),mul(c,B_next))==sc(n)
    for u in [2,3,5,7,11,17]:
        x,y=circle(sc(u)); z=add(x,mul(I,y))
        h=x if xs!=xt else y
        rhs=sub(peval([sc(v) for v in f],x),add(intercept,mul(slope,h)))
        lhs=mul(peval(q,z),inv(power(z,n-1)))
        assert mul(lhs,add(a,add(mul(b,x),mul(c,y))))==rhs
    return b,c,A_top,B_next


def dual_coeffs(alpha):
    a2=mul(alpha,alpha); a3=mul(a2,alpha)
    return [scale(v,pow(4,-1,P)) for v in [O,a3,a2,alpha]]

def folded_sparse_image(eta,b,c,alphas):
    """Reference: materialize 1024 image weights, fold four times."""
    w=[Z]*1024
    eta2=mul(eta,eta)
    w[1023]=eta
    w[1022]=mul(eta2,b)
    w[1021]=scale(mul(eta2,c),-1)
    for alpha in alphas:
        ds=dual_coeffs(alpha)
        w=[total(mul(w[j+r],ds[r]) for r in range(4)) for j in range(0,len(w),4)]
    return w

def compact_image_terminal(eta,b,c,alphas):
    a0,a1,a2,a3=alphas
    a02=mul(a0,a0); a03=mul(a02,a0)
    inner=add(mul(eta,a0),mul(mul(eta,eta),sub(mul(b,a02),mul(c,a03))))
    last=scale(mul(mul(mul(a1,a2),a3),inner),pow(256,-1,P))
    return [Z,Z,Z,last]


def eval_mod(coeffs,x,p):
    out=0
    for c in reversed(coeffs): out=(out*x+c)%p
    return out


def finite_exhaustions():
    # Exhaust fresh eta root counts, including arbitrary prior error and image vector.
    image_cases=0
    for p in [5,7,13]:
        for prior,e1,e2 in product(range(p),repeat=3):
            if e1==e2==0: continue
            assert sum((prior+eta*e1+eta*eta*e2)%p==0 for eta in range(1,p))<=2
            image_cases+=1
    # q=2 shifted batch, arbitrary prior, all residual vectors; rho is nonzero.
    shifted_cases=0
    for p in [5,7,13]:
        for prior,r0,r1 in product(range(p),repeat=3):
            if prior==r0==r1==0:continue
            assert sum((prior-rho*r0-rho*rho*r1)%p==0 for rho in range(1,p))<=2
            shifted_cases+=1
    # Exact sumcheck difference polynomials. A nonzero boundary discrepancy means
    # delta(alpha) has at most 6 zeros. Exhaust binary coefficients over F17.
    relation_cases=0
    p=17
    for coeffs in product(range(2),repeat=7):
        if 4*(coeffs[0]+coeffs[4])%p==0:continue
        assert sum(eval_mod(coeffs,a,p)==0 for a in range(p))<=6
        relation_cases+=1
    # Candidate can depend on an earlier alpha, but is fixed before queries:
    # exhaustive affine code F7, domain five points, degree<=1, all ordered pairs.
    distance_cases=0; query_checks=0
    p=7; domain=list(range(5)); schedules=list(combinations(domain,2))
    polynomials=list(product(range(p),repeat=2))
    for f in polynomials:
        for g in polynomials:
            if f==g:continue
            roots=[x for x in domain if eval_mod(f,x,p)==eval_mod(g,x,p)]
            assert len(roots)<=1
            passing=sum(all(x in roots for x in s) for s in schedules)
            assert passing==comb(len(roots),2)==0
            distance_cases+=1; query_checks+=len(schedules)
    return dict(image_mix_triples=image_cases,shifted_batch_triples=shifted_cases,
                degree_six_relation_discrepancies=relation_cases,
                distinct_final_polynomial_pairs=distance_cases,
                final_pair_query_schedules=query_checks)


def fold_relation_identities():
    rng=random.Random(0x67BA3FF1)
    cases=0
    for length in [4,16,64,256,1024]:
        for case in range(3):
            q=[tuple(rng.randrange(P) for _ in range(4)) for _ in range(length)]
            w=[tuple(rng.randrange(P) for _ in range(4)) for _ in range(length)]
            coeff=[Z]*7
            for j in range(0,length,4):
                a=q[j:j+4]
                d=[scale(w[j+r],pow(4,-1,P)) for r in [0,3,2,1]]
                for r in range(4):
                    for s in range(4):coeff[r+s]=add(coeff[r+s],mul(a[r],d[s]))
            assert scale(add(coeff[0],coeff[4]),4)==total(mul(a,b) for a,b in zip(q,w))
            alpha=[Z,O,tuple(rng.randrange(P) for _ in range(4))][case]
            ds=dual_coeffs(alpha); prim=[O,alpha,mul(alpha,alpha),power(alpha,3)]
            fq=[total(mul(q[j+r],prim[r]) for r in range(4)) for j in range(0,length,4)]
            fw=[total(mul(w[j+r],ds[r]) for r in range(4)) for j in range(0,length,4)]
            assert peval(coeff,alpha)==total(mul(a,b) for a,b in zip(fq,fw))
            cases+=1
    return cases


def fraction_record(x):
    return {'numerator':str(x.numerator),'denominator':str(x.denominator),
            'bits_display_only':log2(x.denominator)-log2(x.numerator)}


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--output');args=parser.parse_args()
    rng=random.Random(0x118415)
    rand=lambda:tuple(rng.randrange(P) for _ in range(4))
    s=circle((11,3,5,7)); t=circle((29,3,5,7))
    pairs=[(s,t),(s,(s[0],scale(s[1],-1)))]
    quotient_cases=0;image_scaled_cases=0
    for n in [8,512]:
        for s0,t0 in pairs:
            b,c,qa,qb=outside_quotient(n,s0,t0)
            quotient_cases+=1
            for ell in [0,25]:
                for gamma in [O,sc(7),(31,3,5,7)]:
                    gscale=power(gamma,ell)
                    assert sub(mul(b,mul(qa,gscale)),mul(c,mul(qb,gscale)))==scale(gscale,n)
                    image_scaled_cases+=1
    terminal_cases=0
    for j in range(80):
        eta=rand();b=rand();c=rand();alphas=[rand() for _ in range(4)]
        if j<4:alphas[j]=Z
        if 4<=j<8:alphas[j-4]=O
        if j==8:eta=Z
        if j==9:b=Z
        if j==10:c=Z
        assert folded_sparse_image(eta,b,c,alphas)==compact_image_terminal(eta,b,c,alphas)
        terminal_cases+=1
    # Re-folding does not determine membership: delta in last block, primal fold zero.
    # E1(delta)=1 for delta=(-alpha^3,0,0,1); a final256-only image test is insufficient.
    for alpha in [Z,O,sc(7),rand()]:
        delta=[scale(power(alpha,3),-1),Z,Z,O]
        assert total(mul(v,w) for v,w in zip(delta,[O,alpha,power(alpha,2),power(alpha,3)]))==Z
        assert delta[3]==O
    eps_dist=Fraction(comb(255,22),comb(2**18,22))
    proposed=Fraction(2+22,K-1)+Fraction(24,K)+eps_dist
    assert proposed<Fraction(1,2**118)
    out={
      'status':'exact calculations and identities verified; proposed gate; no Lean/source/SBF proof',
      'source_review_commit':'67ba3ff1377bbb788d33e2e4a30b5b8b9bf1f5e9',
      'checks':dict(finite_exhaustions(),full_degree_quotient_cases=quotient_cases,
                    quotient_evaluation_points=24,scaled_image_cases=image_scaled_cases,
                    sparse_terminal_cases=terminal_cases,terminal_values_per_case=4,
                    single_fold_kernel_counterexamples=4,relation_convolution_cases=fold_relation_identities()),
      'exact_polynomial_image_invalid_class':{
         'extra_hypotheses':['virtual quotient is exactly a codeword in W before eta',
            'its image vector is nonzero', 'prior relation weight and scalar fixed before fresh nonzero eta',
            'eta*E1+eta^2*E2 is actually installed in the 1024-level relation weights',
            'four degree-six relation rounds with fresh challenges and correct final dot',
            'final256 of degree<=255 fixed before uniform distinct q22 queries',
            'authenticated query values are true virtual-quotient folds',
            'fresh nonzero rho uses shifted Tag-73 joint batch with constant prior term'],
         'adaptive_final_replacement_query_bound':fraction_record(eps_dist),
         'conditional_ideal_acceptance_upper':fraction_record(proposed),
         'formula':'(2+22)/(k-1) + 24/k + choose(255,22)/choose(262144,22)',
         'limitations':['not a bound on arbitrary non-polynomial committed oracles',
             'not actual production acceptance unless source gate instantiated',
             'no FRI/coherence claim or payment witness extracted',
             'no Merkle/FS resource loss, full-view ZK, or CU claim']},
      'image_terminal_formula':'only terminal[3] += alpha1*alpha2*alpha3/256 * (eta*alpha0 + eta^2*(b*alpha0^2-c*alpha0^3))',
      'full_degree_image_residual':'E1=0, E2=512*gamma^ell for T_512',
      'production_changed':False}
    text=json.dumps(out,indent=2)+'\n'
    if args.output:
        with open(args.output,'w') as f:f.write(text)
    print(text,end='')
if __name__=='__main__': main()
