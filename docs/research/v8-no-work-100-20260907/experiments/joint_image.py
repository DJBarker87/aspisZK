#!/usr/bin/env python3
"""Exact restricted ledger. No assumed FS, source, ZK or outside-branch bounds."""
import argparse
from fractions import Fraction
from math import comb, log2
import json

def fraction(x):
    return dict(numerator=str(x.numerator), denominator=str(x.denominator),
                bits_display_only=log2(x.denominator)-log2(x.numerator))

def profile(q, degree, domain, p=2**31-1, extension=4):
    if not 0 < q <= domain or not 0 <= degree < domain:
        raise ValueError("require 0<q<=domain and 0<=degree<domain")
    k=p**extension
    query=Fraction(comb(degree,q),comb(domain,q)) if q<=degree else Fraction(0)
    terms={"image_mix":Fraction(2,k-1),"first_relation":Fraction(6,k),
           "different_final_queries":query,"shifted_batch":Fraction(q,k-1),
           "later_relations":Fraction(18,k)}
    total=sum(terms.values(),Fraction(0))
    assert total==Fraction(q+2,k-1)+Fraction(24,k)+query
    # Independent exact product verifies binomial ratios, including q>degree.
    product=Fraction(1)
    for j in range(q): product*=Fraction(max(degree-j,0),domain-j)
    assert product==query
    encode=lambda x: fraction(x) if x else dict(numerator="0",denominator="1",bits_display_only=None)
    return dict(q=q,degree=degree,domain=domain,field_order=str(k),
                terms={name:encode(x) for name,x in terms.items()},
                total=encode(total),lt_2_neg_118=total<Fraction(1,2**118),
                complete_v8_security=None,fs_lift=None,arbitrary_oracle_bound=None)

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--q',type=int,default=22)
    parser.add_argument('--degree',type=int,default=255);parser.add_argument('--domain',type=int,default=2**18)
    args=parser.parse_args()
    cases=0
    for t in range(2,14):
        for d in range(t):
            for q in range(1,t+1):profile(q,d,t);cases+=1
    result=profile(args.q,args.degree,args.domain)
    result['status']='formal proof complete for causal discrepancy game; source instance and global coverage unresolved'
    result['independent_small_exact_checks']=cases
    if (args.q,args.degree,args.domain)==(22,255,2**18):
        assert result['lt_2_neg_118']
        body=697*16+52+24+22*621+2*296*26
        assert body==40282
        result['canonical_body_model']={
            'fixed_fields':697*16,'roots':52,'retained_work_nonces':24,
            'query_records':22*621,'frontiers':2*296*26,'total':body,
            'image_gate_additional_body_values':0,'over_40000':body-40000,
            'within_accepted_40282':True,'within_40960':True,
            'full_view_hiding_and_source_census_closed':False}
    # This exact framing is proposed research-only code, not deployed behavior.
    image_record=b'aspis-v8-image-gate-v1'
    absorb_bytes=34+len(image_record)
    sha_blocks=lambda n:(n+9+63)//64
    result['proposed_tau_hash_schedule']={
        'record_payload':image_record.decode(),'payload_bytes':len(image_record),
        'absorb_preimage_bytes':absorb_bytes,'squeeze_preimage_bytes':33,'advance_preimage_bytes':33,
        'common_hash_calls':3,'common_sha256_compression_blocks':sha_blocks(absorb_bytes)+2*sha_blocks(33),
        'conservative_bounded_max_hash_calls':1+3*2*4,
        'cu_measured':None,'sampler_source_bridge_proved':False}
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
