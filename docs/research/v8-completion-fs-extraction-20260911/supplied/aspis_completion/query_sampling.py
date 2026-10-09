"""Exact ordered sampling-without-replacement arithmetic; source sampler not yet bound."""
from fractions import Fraction

def all_in_subset(domain:int,subset:int,queries:int)->Fraction:
    if domain<1 or not 0<=subset<=domain or not 0<=queries<=domain:
        raise ValueError('invalid sample cardinalities')
    result=Fraction(1)
    for i in range(queries):
        if i>=subset:return Fraction(0)
        result*=Fraction(subset-i,domain-i)
    return result

def with_replacement_ceiling(domain:int,subset:int,queries:int)->Fraction:
    if domain<1 or not 0<=subset<=domain or queries<0:
        raise ValueError('invalid sample cardinalities')
    return Fraction(subset,domain)**queries
