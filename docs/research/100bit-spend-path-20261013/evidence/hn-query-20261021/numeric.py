#!/usr/bin/env python3
"""Independent exact rational check of the proved envelope's endpoint."""
from fractions import Fraction as F
import json
from math import isqrt
from pathlib import Path
import re
HERE=Path(__file__).resolve().parent
source=(HERE.parent.parent/'lean/BinPerQueryNumeric.lean').read_text()
m=int(re.search(r'def Qmax : Nat := (\d+)',source)[1])
a=6*2**198
b=13932*2**198+15*2**345-2**354
c=6*1161**2*2**198+510*2**345+2**328+1-2**354
root=(-b+isqrt(b*b-4*a*c))//(2*a)
def gap(q):
    return F(6*(q+1161)**2,2**256)+F(15*(q+34),2**109)+F(1,2**126)+F(1,2**454)-F(q+1,2**100)
assert m==root and 2**153<m
assert gap(0)<0 and gap(m)<0 and gap(m+1)>0
assert gap(m)*2**454==a*m*m+b*m+c
result={'Qmax':m,'above_2_pow_153':True,'gap_zero':str(gap(0)),
        'gap_Qmax':str(gap(m)),'gap_next':str(gap(m+1)),
        'method':'integer quadratic root and exact Fraction arithmetic; interval proved symbolically in Lean'}
(HERE/'numeric.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
