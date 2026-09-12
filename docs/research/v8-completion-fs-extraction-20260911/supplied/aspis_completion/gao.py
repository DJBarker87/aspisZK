"""Quadratic-time prime-field Gao reference decoder with checked output.

Still not the selected circle/QM31 extractor. Unlike the Gaussian reference,
this is a practical algorithmic starting point for larger samples; profile
basis conversion and allowed authenticated sample production stay outside.
"""
from __future__ import annotations
from typing import Sequence
from .polynomial import require_prime, trim, evaluate, multiply, divmod_poly, DecodeError


def subtract(a: Sequence[int], b: Sequence[int], p: int) -> list[int]:
    out=[0]*max(len(a),len(b))
    for i in range(len(out)):
        out[i]=((a[i] if i<len(a) else 0)-(b[i] if i<len(b) else 0))%p
    return trim(out,p)


def vanishing(xs: Sequence[int], p: int) -> list[int]:
    out=[1]
    for x in xs:
        out=multiply(out,[-x,1],p)
    return out


def interpolate(xs: Sequence[int], ys: Sequence[int], p: int,
                g: Sequence[int] | None = None) -> list[int]:
    require_prime(p)
    if len(xs)!=len(ys) or len(set(x%p for x in xs))!=len(xs):
        raise DecodeError('interpolation dimensions or duplicate points')
    if not xs:
        return []
    g=list(g) if g is not None else vanishing(xs,p)
    derivative=[(i*g[i])%p for i in range(1,len(g))]
    out=[0]*len(xs)
    for x,y in zip(xs,ys):
        basis,rem=divmod_poly(g,[-x,1],p)
        if rem:
            raise DecodeError('provided vanishing polynomial is inconsistent')
        denominator=evaluate(derivative,x,p)
        if not denominator:
            raise DecodeError('zero Lagrange denominator')
        scale=y*pow(denominator,-1,p)%p
        for i,c in enumerate(basis):out[i]=(out[i]+scale*c)%p
    if any(evaluate(out,x,p)!=y%p for x,y in zip(xs,ys)):
        raise AssertionError('interpolant validation failed')
    return trim(out,p)


def gao_decode(xs: Sequence[int], ys: Sequence[int], k: int, t: int, p: int) -> tuple[int,...]:
    require_prime(p)
    if k<1 or t<0 or len(xs)!=len(ys) or len(xs)<k+2*t:
        raise DecodeError('need n>=k+2t')
    if len(set(xs))!=len(xs) or any(not 0<=x<p for x in xs) or any(not 0<=y<p for y in ys):
        raise DecodeError('noncanonical or duplicate sample')
    g=vanishing(xs,p); r=interpolate(xs,ys,p,g)
    if not r:
        return (0,)*k
    r0,r1=g,r; v0,v1=[],[1]
    # r_i = u_i*G + v_i*R. Stop once the numerator has degree < k+t.
    # The final quotient and distance are checked; no blind Euclid success.
    while r1 and len(r1)>k+t:
        q,r2=divmod_poly(r0,r1,p)
        v2=subtract(v0,multiply(q,v1,p),p)
        r0,r1=r1,r2;v0,v1=v1,v2
    if not v1 or len(v1)>t+1:
        raise DecodeError('locator degree outside corruption budget')
    candidate,rem=divmod_poly(r1,v1,p)
    if rem or len(candidate)>k:
        raise DecodeError('nondivisible or oversized candidate')
    candidate += [0]*(k-len(candidate))
    if sum(evaluate(candidate,x,p)!=y for x,y in zip(xs,ys))>t:
        raise DecodeError('candidate exceeds sample-error bound')
    return tuple(candidate)
