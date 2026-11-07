from fractions import Fraction as F
import math
P=lambda k: F(2)**k
def gap(x, extra=0):
    acc = 6*(x+2965)**2/P(256)
    return 6*((x+1161)**2+(x+2965)**2)/P(256) + (x+34)*F(15)/P(109) + 1/P(126)+1/P(454) + extra*acc - F(x+1)/P(100)
def maxq(extra):
    # gap is convex quadratic; find largest x with gap<=0 by bisection
    lo, hi = 0, 2**160
    assert gap(lo,extra)<=0 and gap(hi,extra)>0
    while hi-lo>1:
        m=(lo+hi)//2
        if gap(m,extra)<=0: lo=m
        else: hi=m
    return lo
m0=maxq(0); m1=maxq(1)
print("maxQueries total      ", m0, math.log2(m0), m0==7388980242446479800895501321004157112314840375)
print("maxQueries total+acct ", m1, math.log2(m1), m1==4925986828297653200597000880669438074876558273)
print("ratio", m1/m0)
print("Q=0 margin A:", float((1/P(100)-(gap(0,1)+F(1)/P(100)))*P(108)))
