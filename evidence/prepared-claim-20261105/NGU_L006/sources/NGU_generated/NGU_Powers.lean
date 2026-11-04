import NGU_ClaimOps
import NGU_ArrayMap
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGU_Powers
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues NGU_Carriers
abbrev claim := NGU_ClaimOps.claim

theorem source (N : Usize) (x : NE) (hx : canonE x) :
 ∃ out, FIo_Native.weights.powers N x=ok out ∧
  AspisR1CurrentPreparedClaim.ClaimPowers.powers N (claim x)=ok (arr claim out) := by
 obtain ⟨out,call,model,_⟩ := NFW_PowersCohort.source N x hx
 have same := AspisR1ClaimPreparedBridge.powersPublic_success _ _ model
 exact ⟨out,call,same⟩

#print axioms source
end AspisR1.NGU_Powers
end
