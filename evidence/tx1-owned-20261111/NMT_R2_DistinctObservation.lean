import NMT_R2_DistinctValue
import NMT_R2_EmittedData
set_option autoImplicit false
noncomputable section
namespace NMT_R2_DistinctObservation
open Aeneas Aeneas.Std NMT_345 RSL NMT_R2_EmittedData
attribute [local instance] Classical.propDecidable

theorem law {W : Type} (s : Selected W) (env : Env) :
 RS.ofExcept (requireDistinct [account s.proofAccount,account s.publicAccount,account s.checkpointAccount]) env
  (observe id (distinctCall s)) := by
 rw [NMT_R2_DistinctValue.source]
 have key_eq (a b : Key) : key a = key b ↔ a = b :=
  ⟨fun h => key_injective h,fun h => congrArg key h⟩
 by_cases h01 : s.proofAccount.key = s.publicAccount.key <;>
  by_cases h02 : s.proofAccount.key = s.checkpointAccount.key <;>
  by_cases h12 : s.publicAccount.key = s.checkpointAccount.key <;>
  simp [requireDistinct,distinctKeys,account,key_eq,eq_comm,h01,h02,h12,RS.ofExcept,
   Spec.pure,observe,rustResult,pe]
#print axioms law
end NMT_R2_DistinctObservation
end
