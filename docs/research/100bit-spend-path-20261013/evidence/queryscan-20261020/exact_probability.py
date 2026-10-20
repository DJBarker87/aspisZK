#!/usr/bin/env python3
"""Exact occupancy calculation; independent arithmetic evidence, not Lean proof."""
from fractions import Fraction
from decimal import Decimal, localcontext
import json,pathlib,hashlib
N=2**18
# Count strings by number of distinct values. Multiplication by N-j creates a
# new value; multiplication by j repeats an existing one. States >21 can
# never return, so truncation is exact for the exhaustion event.
a=[1]+[0]*21
for n in range(64):
    a=[j*a[j]+((N-j+1)*a[j-1] if j else 0) for j in range(22)]
p=Fraction(sum(a),N**64)
u=Fraction(N**21*21**64,N**64)
assert p<=u<=Fraction(1,2**454)<Fraction(1,2**100)
with localcontext() as ctx:
    ctx.prec=40
    d=Decimal(p.numerator)/Decimal(p.denominator)
    bits=-(d.ln()/Decimal(2).ln())
result={'space_positions':N,'candidate_words':64,'failure_distinct_max':21,
        'exact_probability_numerator':str(p.numerator),'exact_probability_denominator':str(p.denominator),
        'decimal':str(d),'negative_log2':str(bits),'counting_bound':'N^21 * 21^64 / N^64',
        'proved_power_bound':'2^-454','eight_attempt_union_bound':'8 * 2^-454 = 2^-451',
        'scope':'Independent uniform 18-bit words; source/ROM coupling is not asserted.',
        'script_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()}
pathlib.Path(__file__).with_name('exact-probability.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
