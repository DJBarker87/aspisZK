import XSf_Closed
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers
set_option autoImplicit false
namespace XSf_Nonvacuity
open AspisR1ClaimPreparedBridge

/-- A constructive successful powers/fold inhabitant; all arrays and outputs
are produced by the existing symbolic theorems, without numeral normalization. -/
theorem powers_and_sum :
 ∃ (g : XSa_DotRun.Coeff) (k : XRy_ClaimSumStep.Seven) (out : C.E),
 powersPublic 29#usize XRy_Powers.one=ok g ∧ XSa_DotRun.canonical g ∧
 XRn_Join_powers XRy_Powers.one 7 XRy_Powers.one=ok k.val ∧
 XSa_DotCarriers.ops.powers 7#usize (toClaimE XRy_Powers.one)=ok (arr toClaimE k) ∧
 XRy_ClaimSumStep.canonical k ∧ XRy_WideMultiply.Canonical out ∧
 (k.val.zip (XSa_ClaimInitial.initial XRy_Powers.zero).val).foldlM
   XSa_ClaimPairs.addTerm XRy_Powers.zero=ok out ∧
 AspisR1CurrentPreparedClaim.verifier.prepared_claim_sum (arr toClaimE k)
   (arr toClaimE (XSa_ClaimInitial.initial XRy_Powers.zero))=ok (toClaimE out) := by
 obtain ⟨g,_,hg,hgc⟩ := XSa_PowersDimensions.twenty_nine XRy_Powers.one XRy_Powers.one_canonical
 obtain ⟨k,hk,hkt,hkc⟩ := XSa_PowersDimensions.seven XRy_Powers.one XRy_Powers.one_canonical
 obtain ⟨out,hc,hr,ht⟩ := XSa_ClaimSumJoin.paired k (XSa_ClaimInitial.initial XRy_Powers.zero)
   hkc (XSa_ClaimInitial.canonical XRy_Powers.zero XRy_ClaimSum.zero_canonical)
 exact ⟨g,k,out,hg,hgc,hk,hkt,hkc,hc,hr,ht⟩

#print axioms powers_and_sum
end XSf_Nonvacuity
