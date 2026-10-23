#!/usr/bin/env python3
"""Materialize the emitted original-ABI reference with explicit primitive ports."""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2]
B=R/'docs/research/100bit-spend-path-20261013'
E=B/'evidence/s126-current-caller-20261021/s1-claim-owned-reference/borrowed-abi-extraction'
raw=E/'generated/AspisS1OwnedNestedClaim/Funs.lean'
s=raw.read_text();s=s[s.index('/-- [aspis_r1_verify_prepared_prefix::verifier::owned_scalar]'):]
s=s.replace('end AspisS1OwnedNestedClaim','end AspisR1CurrentPreparedClaim')
s=s.replace('fast_pairing.EbyKDot','D')
for old,new in [('weights.field','ops.field'),('weights.powers','ops.powers'),
                ('aspis_core.field.WideExact.impl.c0','ops.c0'),
                ('D.new','ops.newDot'),('D.push','ops.pushDot'),('D.finish','ops.finishDot'),
                ('core.result.Result.is_err','ownedIsErr')]:s=s.replace(old,new)
ops_names=['owned_scalar','owned_push','owned_claim_loops_loop0_loop0.body',
           'owned_claim_loops_loop0_loop0','owned_claim_loops_loop0.body',
           'owned_claim_loops_loop0','owned_claim_loops','prepared_claim_owned']
pattern=r'verifier\.('+ '|'.join(re.escape(n) for n in sorted(ops_names,key=len,reverse=True))+r')(?=[\s(])'
s=re.sub(pattern,lambda m:m[0]+' ops',s)
for n in ops_names:
    old='def verifier.'+n+' ops\n';assert s.count(old)==1,n
    s=s.replace(old,'def verifier.'+n+'\n  {D : Type} (ops : ClaimDotOps D)\n')
all_names=ops_names+['owned_sum_loop.body','owned_sum_loop','owned_sum']
pattern=r'verifier\.('+ '|'.join(re.escape(n) for n in sorted(all_names,key=len,reverse=True))+r')(?=[\s(])'
s=re.sub(pattern,lambda m:'verifier.borrowed_abi.'+m[1],s)
prefix='''import S1ClaimSliceCarrierV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1CurrentPreparedClaim
'''
out=B/'lean-candidates/s126-caller-boundary-20261021/S1ClaimBorrowedAbiNativeV1.lean'
out.write_text(prefix+s+'\n#print axioms AspisR1CurrentPreparedClaim.verifier.borrowed_abi.prepared_claim_owned\n')
(E/'materialization.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',
    raw_sha256=hashlib.sha256(raw.read_bytes()).hexdigest(),candidate_sha256=hashlib.sha256(out.read_bytes()).hexdigest(),
    qualification='Emitted original borrowed sem/y1/g ABI; complete retained nominal carriers and explicit existing ClaimDotOps. No fixed array extent, allocation or semantic owner transfer added. Primitive installation, native original/reference and actual caller binding remain explicit.'),indent=2)+'\n')
