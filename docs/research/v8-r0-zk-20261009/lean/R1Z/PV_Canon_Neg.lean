import R1Z.PV_Canon_Carrier
import R1Z.PV_CB_CurrentNeg
import R1Z.ProverCommitNativeNeg49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result
 theorem current_neg (x : U32) (hx : M x) :
    ∃ z, ProverRwP7CurrentFieldSource.aspis_core.field.M31.neg x = .ok z ∧ M z := by
  change ∃ z, PV_CB_CurrentNeg.source x = .ok z ∧ M z
  rw [PV_CB_CurrentNeg.native]
  obtain ⟨z,hz,hc,_⟩ := ProverCommitNativeNeg49.neg_word x hx
  exact ⟨z,hz,hc⟩
#print axioms current_neg
end R1Z.PV_Canon
