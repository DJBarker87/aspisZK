import NMT_345Distinct
import NMT_R2_DistinctReference
set_option autoImplicit false
noncomputable section
namespace NMT_R2_DistinctValue
open Aeneas Aeneas.Std NMT_345
attribute [local instance] Classical.propDecidable

theorem source {W : Type} (s : Selected W) : distinctCall s =
 .ok (if s.proofAccount.key = s.publicAccount.key ∨
  s.proofAccount.key = s.checkpointAccount.key ∨ s.publicAccount.key = s.checkpointAccount.key
  then .Err .InvalidArgument else .Ok ()) := by
 unfold distinctCall
 rw [NHJ_DistinctPacket.three,NMT_R2_DistinctReference.source]
 by_cases h : s.proofAccount.key = s.publicAccount.key ∨
  s.proofAccount.key = s.checkpointAccount.key ∨ s.publicAccount.key = s.checkpointAccount.key
 · simp only [h,if_true,mapOuter,mapCore,fromPE]
 · simp only [h,if_false,mapOuter,mapCore]
#print axioms source
end NMT_R2_DistinctValue
end
