#!/usr/bin/env python3
"""Expose extracted primitive ports using the existing complete ClaimDotOps.
No generated axiom/template is imported into the checked candidate.
"""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2]
B=R/'docs/research/100bit-spend-path-20261013'
E=B/'evidence/s126-current-caller-20261021/s1-claim-owned-reference'
raw=E/'raw-generated/AspisS1OwnedNestedClaim/Funs.lean'
s=raw.read_text();s=s[s.index('/-- [aspis_r1_verify_prepared_prefix::verifier::owned_scalar]'):]
s=s.replace('end AspisS1OwnedNestedClaim','end AspisR1CurrentPreparedClaim')
s=s.replace('fast_pairing.EbyKDot','D')
for old,new in [('weights.field','ops.field'),('weights.powers','ops.powers'),
                ('aspis_core.field.WideExact.impl.c0','ops.c0'),
                ('D.new','ops.newDot'),('D.push','ops.pushDot'),('D.finish','ops.finishDot'),
                ('core.result.Result.is_err','ownedIsErr')]:
    s=s.replace(old,new)
names=['owned_scalar','owned_push','owned_claim_loops_loop0_loop0.body',
       'owned_claim_loops_loop0_loop0','owned_claim_loops_loop0.body',
       'owned_claim_loops_loop0','owned_claim_loops','prepared_claim_owned']
pattern=r'verifier\.('+ '|'.join(re.escape(n) for n in sorted(names,key=len,reverse=True))+r')(?=[\s(])'
s=re.sub(pattern,lambda m:m[0]+' ops',s)
for n in names:
    old='def verifier.'+n+' ops\n'
    assert s.count(old)==1,n
    s=s.replace(old,'def verifier.'+n+'\n  {D : Type} (ops : ClaimDotOps D)\n')
# Generalize only private helper array extents. The public extracted wrapper
# stays exactly928; its calls specialize these unchanged bodies to928.
marker='/-- [aspis_r1_verify_prepared_prefix::verifier::prepared_claim_owned]'
a=s.index(marker)
private=s[:a].replace('Array Std.U8 928#usize','Array Std.U8 N')
for n in names:
    if n in ['owned_push','prepared_claim_owned']:continue
    header='def verifier.'+n+'\n  {D : Type} (ops : ClaimDotOps D)\n'
    assert private.count(header)==1,n
    private=private.replace(header,'def verifier.'+n+'\n  {D : Type} {N : Usize} (ops : ClaimDotOps D)\n')
s=private+s[a:]
prefix='''import S1ClaimAllLoopsBoundedV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1CurrentPreparedClaim
/-- Documented Result::is_err: no callbacks or state effects. -/
def ownedIsErr {T E : Type} (r : core.result.Result T E) : Result Bool :=
  ok (match r with | .Ok _ => false | .Err _ => true)

'''
out=B/'lean-candidates/s126-caller-boundary-20261021/S1ClaimOwnedNestedModelV1.lean'
out.write_text(prefix+s+'\n#print axioms AspisR1CurrentPreparedClaim.verifier.prepared_claim_owned\n#print axioms AspisR1CurrentPreparedClaim.verifier.owned_claim_loops\n#print axioms AspisR1CurrentPreparedClaim.verifier.owned_sum\n')
(E/'materialization.json').write_text(json.dumps(dict(
    schema='focused-extractor-proof-packet-v1', raw_sha256=hashlib.sha256(raw.read_bytes()).hexdigest(),
    candidate_sha256=hashlib.sha256(out.read_bytes()).hexdigest(),
    qualification='Generated bodies retained; original complete retained nominal carriers, existing zero/trace/add/mul definitions, explicit arbitrary ClaimDotOps ports, documented Result::is_err. Private helper extents are generalized to N; the public wrapper is exactly928, with the same body at that specialization. No custom axioms. Retained carrier/source/P6/native equivalence remains a separate gate.'),indent=2)+'\n')
