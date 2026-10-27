import XSa_ClaimPairs
import XSa_FoldCongr
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRy_ClaimSumStep XSa_ClaimPairs
set_option autoImplicit false
namespace XSa_ClaimSumJoin
open AspisR1ClaimPreparedBridge

theorem fold (k parts : Seven) (sum : C.E) :
 (k.val.zip parts.val).foldlM addTerm sum =
 XRy_ClaimSumLoop.run k parts 7 0#usize sum := by
 rw [XRy_IndexedSum.run_fold 7 k parts 0#usize sum (by scalar_tac)]
 have he : List.range' (0#usize).val 7=List.range 7 := rfl
 rw [he,←pairs,XSa_GenericPairs.fold_map]
 apply XSa_FoldCongr.fold
 intro i hi acc
 exact (XSa_ClaimPairs.step k parts acc i (List.mem_range.mp hi)).symm

theorem paired (k parts : Seven) (hk : canonical k) (hp : canonical parts) :
 ∃ out, XRy_WideMultiply.Canonical out ∧
 (k.val.zip parts.val).foldlM addTerm XRy_Powers.zero=ok out ∧
 AspisR1CurrentPreparedClaim.verifier.prepared_claim_sum (arr toClaimE k) (arr toClaimE parts)=
 ok (toClaimE out) := by
 obtain ⟨out,hc,hr,ht⟩ := XRy_ClaimSum.sum k parts hk hp
 exact ⟨out,hc,(fold k parts XRy_Powers.zero).trans hr,ht⟩

#print axioms fold
#print axioms paired
end XSa_ClaimSumJoin
