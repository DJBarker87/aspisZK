"""Review cross-check and explicit accepted-discarded coverage budgets.

No family-coverage theorem, complete security bound, or CU measurement is claimed.
Independent falling products and tree recurrence check the supplied ZIP model.
The ZIP module is optional and is imported only after its manual review.
"""
import argparse
import contextlib
from fractions import Fraction as F
from functools import lru_cache
import importlib.util
import io
import json
from itertools import product
from math import comb, log2
from pathlib import Path

P = 2**31-1
K = P**4
T = 2**18
J = 9557
TARGET = F(1,2**100)
# Eight fixed K1.5 categories, not just the semantic sumcheck.
K15 = F(30500+292800+73100+1+1+2+24+2,K-1)
FOLD = F(28,K-1)+(1-F(28,K-1))*F(3,K-1)

def query(q, support=J):
    r = F(1)
    for i in range(q):
        r *= F(support-i,T-i)
    assert r == F(comb(support,q),comb(T,q))
    return r

@lru_cache(None)
def frontier(depth,q):
    if depth==0:
        assert q==1
        return 0
    half=2**(depth-1)
    options=[]
    for left in range(max(0,q-half),min(q,half)+1):
        right=q-left
        if left==0: options.append(1+frontier(depth-1,right))
        elif right==0: options.append(1+frontier(depth-1,left))
        else: options.append(frontier(depth-1,left)+frontier(depth-1,right))
    return max(options)

def rational(x):
    r={"numerator":str(x.numerator),"denominator":str(x.denominator)}
    if x>0: r["bits_display_only"]=log2(x.denominator)-log2(x.numerator)
    return r

def without_display(x):
    if isinstance(x,dict):
        return {k:without_display(v) for k,v in x.items()
                if k not in ("bits_display_only","fraction_of_2minus100_budget")}
    if isinstance(x,list): return [without_display(v) for v in x]
    return x

def tiny_relaxed_cover():
    """Exhaustive constants-code analogue; not the 1024-dimensional theorem.
    Every high-agreement adaptive candidate is covered in THIS tiny game,
    despite failure of old same-support recovery. No probability is simulated.
    """
    p=17
    rows=[(0,0,0)]*2
    rows += [(((2*s+1)*(2*s+2))%p,(-(4*s+3))%p,1) for s in range(6)]
    tuples=list(product(range(p),repeat=3))
    agreement={c:sum(c==row for row in rows) for c in tuples}
    old=[c for c in tuples if agreement[c]>=3]
    relaxed=[c for c in tuples if agreement[c]>=2]
    assert old==[] and relaxed==[(0,0,0)]
    high=covered=old_same_support=0
    for gamma in range(1,p):
        values=[(r[0]+gamma*r[1]+gamma*gamma*r[2])%p for r in rows]
        for candidate in range(p):
            support=[i for i,v in enumerate(values) if v==candidate]
            if len(support)<3: continue
            high+=1
            represented=[c for c in relaxed if (c[0]+gamma*c[1]+gamma*gamma*c[2])%p==candidate]
            covered+=bool(represented)
            old_same_support+=any(all(rows[i]==c for i in support) for c in represented)
    assert high==covered==12 and old_same_support==0
    return {"field":p,"width":3,"fibres":8,"code":"constant component polynomials",
            "exhaustive_tuples":len(tuples),"gamma_candidate_cases":16*17,
            "old_family_size":0,"relaxed_family_size":1,
            "high_agreement_branches":high,"relaxed_on_curve_covered":covered,
            "old_same_support_recoverable":old_same_support,
            "scope":"toy game only; no inference to full Aspis adaptive coverage"}

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--review-dir", type=Path)
    args=parser.parse_args()
    reviewed=None
    if args.review_dir:
        spec=importlib.util.spec_from_file_location("supplied_recovery_review",args.review_dir/"review.py")
        module=importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        output=io.StringIO()
        with contextlib.redirect_stdout(output): module.main()
        reviewed=json.loads(output.getvalue())
        packaged=json.loads((args.review_dir/"results.json").read_text())
        assert without_display(reviewed)==without_display(packaged)

    rows=[]
    for q in (21,22,23,24):
        b=query(q)
        one=b+(1-b)*FOLD
        f=frontier(18,q)
        body=697*16+24+52+621*q+52*f
        capacity=(TARGET-K15)//one
        for targets in (1,34,35,100):
            subtotal=targets*one+K15
            remaining=TARGET-subtotal
            rows.append({"field_degree":4,"queries":q,"targets_assumed":targets,
                "body_model_bytes":body,"extra_over_40282":body-40282,
                "maximum_frontier_per_tree":f,"internal_hashes_both_trees":2*(q+f-1),
                "leaf_hashes_both_trees":2*q,
                "conditional_subtotal":rational(subtotal),
                "positive_budget_for_coverage_and_all_other_omissions":remaining>0,
                "remaining_absolute_budget":rational(remaining),
                "remaining_fraction_of_2minus100":rational(remaining/TARGET),
                "max_target_count_if_no_other_terms":capacity,
                "coverage_proved":False,"full_view_hiding_proved":False,"full_transaction_CU":None})
        if reviewed:
            supplied=next(x for x in reviewed["qm31_list_loss_screens"] if x["queries"]==q)
            value=supplied["100_target_fixed_fold_plus_semantic_screen"]
            assert F(int(value["numerator"]),int(value["denominator"]))==100*one+K15
            assert body==supplied["body_model"]
    q5=[]
    for q in (21,22,23):
        subtotal=query(q)+F(2*336869026605739+396430+3+q+18,P**5-1)+F(9396508281246,P**5)
        body=641*20+24+52+668*q+52*frontier(18,q)
        q5.append({"queries":q,"body_model_bytes":body,"extra_over_40282":body-40282,
            "conditional_known_stage_subtotal":rational(subtotal),
            "budget_fraction_used":rational(subtotal/TARGET),
            "field_source_hiding_ports":"unresolved","full_transaction_CU":None})
        if reviewed:
            supplied=next(x for x in reviewed["quintic_screens"] if x["queries"]==q)
            value=supplied["known_stage_conditional_subtotal"]
            assert F(int(value["numerator"]),int(value["denominator"]))==subtotal
            assert body==supplied["body_model"]

    # Explicit same-support-cover obstruction: lowering the close-family floor
    # retains its cardinality, but cannot yield the old sharedSupport premise.
    johnson=[]
    for floor in (38230,38229,38228,38227):
        n,d=2**20,1024
        cap=n*(floor-d)//(floor*floor-n*d)
        assert cap==100
        assert (floor*floor-n*d)*101 > n*(floor-d)
        johnson.append({"minimum_joint_symbols":floor,"johnson_cap":cap,
                        "decoder_filter_removed":floor<38230,
                        "adaptive_cover_proved":False})
    print(json.dumps({"review_exact_output_reproduced":reviewed is not None,
        "supplied_small_cases":reviewed["tests"] if reviewed else None,
        "qm31_cover_budget_rows":rows,"quintic_controls":q5,
        "toy_relaxed_cover":tiny_relaxed_cover(),
        "relaxed_joint_list_arithmetic":johnson,
        "caveat":"Close-list cardinality and fixed-target match upper bounds have opposite inequalities; they cannot be combined as an adaptive cover theorem."},indent=2))

if __name__=="__main__": main()
