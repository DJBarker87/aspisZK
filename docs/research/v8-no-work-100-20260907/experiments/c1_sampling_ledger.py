#!/usr/bin/env python3
"""Exact conditional extractor sampling bound, NOT a V8 acceptance bound."""
from fractions import Fraction
from math import comb, log2
from itertools import combinations
import json

def tail(T, B, n, threshold):
    return Fraction(sum(comb(B,j)*comb(T-B,n-j)
                        for j in range(max(threshold, n-(T-B)), min(B,n)+1)),comb(T,n))

def results():
    checks=0
    for T in range(1,9):
        for B in range(T+1):
            for n in range(T+1):
                counts=[sum(i<B for i in s) for s in combinations(range(T),n)]
                for t in range(n+2):
                    assert tail(T,B,n,t)==Fraction(sum(j>=t for j in counts),len(counts))
                    checks+=1
    T,B,n,k=262144,16535,513,1025
    symbol_radius=(4*n-k)//2
    bad_threshold=symbol_radius//4+1
    e=tail(T,B,n,bad_threshold)
    # In 4096 uniform draws, exhaustion before 513 distinct points requires
    # at least 3584 repeats. Each repeat before completion has probability
    # <=512/T. Union over subsets is bounded by 2^4096.
    abort=Fraction(1,2**28160)
    total=e+abort
    assert e<Fraction(1,2**137) and total<Fraction(1,2**137)
    assert 2*B+256<T
    return dict(status='arithmetic verified; conditional mathematical decoder argument; source/Lean port unresolved',
        event='specified private-sample unique decoder fails GIVEN a fixed canonical C1 within B common fibres of a source code tuple',
        T=T,common_bad_fibres_max=B,private_sample_fibres=n,scalar_evaluations=4*n,
        ambient_CM31_RS_dimension=k,correctable_symbol_errors=symbol_radius,
        bad_fibres_needed_for_decoder_failure=bad_threshold,
        sample_tail_numerator=str(e.numerator),sample_tail_denominator=str(e.denominator),
        sample_tail_display_bits=log2(e.denominator)-log2(e.numerator),
        sampler_abort_upper_bound='2^-28160',combined_exact_less_than='2^-137',
        finite_exhaustive_hypergeometric_checks=checks,
        prerequisites=['fixed received C1 before independent private sampling',
            'canonical semantic entries and a common B-fibre corruption support',
            'actual circle tensor encoder embeds in z^-512 times degree<=1024 CM31 polynomials',
            'distinct sample points and correct Gao unique decoding',
            'source re-encoding, base-field descent and literal checked witness validation'],
        unique_C1_projection_inequality=dict(lhs=2*B+256,rhs=T),
        timing='uniqueness fixes the C1 projection at C1 prefix WHERE a close code tuple exists; it does not prove existence at every prefix',
        sampling_law='ideal independent uniform draws, first 513 distinct, 4096-draw abort; permutation symmetry gives uniform output subsets conditional on completion',
        prototype_law='fixed SHA test coins only; no measured randomness/security claim',
        no_column_union='one common bad-fibre set controls all 16 semantic columns',
        proof_body_bytes=40282,extra_protocol_bytes=0,extra_verifier_queries=0,
        global_accepted_extraction_failure=None,FS_lift=None,grinding_credit_bits=0)

if __name__=='__main__': print(json.dumps(results(),indent=2))
