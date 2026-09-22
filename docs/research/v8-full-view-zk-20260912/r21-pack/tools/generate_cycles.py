#!/usr/bin/env python3
"""Exact integer correction certificate. Optional actual-stage ORDER check.

With no --stage-table, uses the retained independent model inventory. This is
not a claim that a new Rust/source/PCS profile has been run.
"""
import argparse,ast,collections,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]

def cycles(order):
    seen=set();out=[]
    for start in range(len(order)):
        if start in seen: continue
        c=[];at=start
        while at not in seen:
            seen.add(at);c.append(at);at=order[at]
        assert at==start
        if len(c)>1: out.append(c)
    return out

def complete(pads):
    n=1024;k=89
    assert len(pads)==k and len(set(pads))==k
    assert all(0<=r<n-1 for r in pads)
    assert all(r>j for j,r in enumerate(pads)), "forest proof needs this fixed-inventory property"
    order=list(range(n));order[:k]=pads
    for start in range(k):
        if start in pads: continue
        at=start;seen=set()
        while at<k:
            assert at not in seen,'unexpected forced closed component'
            seen.add(at);at=pads[at]
        order[at]=start
    assert sorted(order)==list(range(n))
    return order

def certify(order):
    # Matrix has w-row / v-column indexing; P* w is w[order[j]].
    actual=collections.Counter();expected=collections.Counter();products=[]
    for c in cycles(order):
        anchor=c[0]
        for k in range(1,len(c)):
            row=c[k];previous=c[k-1]
            products.append([row,anchor,previous,row])
            for a,b,s in [(row,previous,1),(row,row,-1),(anchor,previous,-1),(anchor,row,1)]:
                actual[a,b]+=s
    for j,r in enumerate(order):
        expected[r,j]+=1;expected[j,j]-=1
    clean=lambda d:{k:v for k,v in d.items() if v}
    assert clean(actual)==clean(expected)
    return {'cycles':cycles(order),'bilinear_factors':products,
            'rank_I_minus_P':sum(len(c)-1 for c in cycles(order)),
            'cycle_lengths':dict(sorted(collections.Counter(map(len,cycles(order))).items())),
            'integer_operator_equality':True}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--stage-table',type=Path)
    a=p.parse_args()
    old=json.loads((ROOT/'evidence/baseline_order.json').read_text())
    if a.stage_table:
        s=a.stage_table.read_text()
        match=re.search(r'ORDER\s*:\s*\[usize;\s*1024\]\s*=\s*(\[[^;]+\]);',s)
        if match is None: raise SystemExit('Cannot locate exact ORDER declaration')
        actual=ast.literal_eval(match[1]);assert actual==old,'Actual stage differs: rebase, do not waive this check'
    new=complete(old[:89])
    assert new[:89]==old[:89] and new[1023]==1023
    assert {j for j in range(1024) if old[j]!=j}=={j for j in range(1024) if new[j]!=j}
    result={'scope':'exact model-order integer certificate','actual_stage_table_checked':bool(a.stage_table),
            'current':certify(old),'candidate':certify(new),'candidate_order':new,
            'same_first_89':True,'same_pivot':True,'same_163_changed_positions':True}
    (ROOT/'evidence/cycle_certificate.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k]['rank_I_minus_P'] for k in ('current','candidate')}))
if __name__=='__main__': main()
