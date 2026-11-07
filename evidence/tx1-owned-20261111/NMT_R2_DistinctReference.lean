import NMT_345Distinct
import NMT_R2_WrapAdd
set_option autoImplicit false
noncomputable section
namespace NMT_R2_DistinctReference
open Aeneas Aeneas.Std NMT_345
attribute [local instance] Classical.propDecidable

theorem source {W : Type} (s : Selected W) :
 NGL_DistinctInduction.reference (oldArray (selectedArray s)) =
 .ok (if s.proofAccount.key = s.publicAccount.key ∨
  s.proofAccount.key = s.checkpointAccount.key ∨ s.publicAccount.key = s.checkpointAccount.key
  then .Err .InvalidArgument else .Ok ()) := by
 have step0 := NMT_R2_WrapAdd.source 0#usize 1#usize 1#usize rfl
 have step1 := NMT_R2_WrapAdd.source 1#usize 1#usize 2#usize rfl
 have step2 := NMT_R2_WrapAdd.source 2#usize 1#usize 3#usize rfl
 by_cases h01 : s.proofAccount.key = s.publicAccount.key <;>
  by_cases h02 : s.proofAccount.key = s.checkpointAccount.key <;>
  by_cases h12 : s.publicAccount.key = s.checkpointAccount.key <;>
  simp [NGL_DistinctInduction.reference,NGL_DistinctInduction.outer.eq_def,
   NGL_DistinctInduction.inner.eq_def,NGL_DistinctInduction.keyAt,oldArray,selectedArray,
   toAccount,Array.make,eq_comm,step0,step1,step2,h01,h02,h12]
#print axioms source
end NMT_R2_DistinctReference
end
