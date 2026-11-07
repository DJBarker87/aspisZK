import NNH_MResultProjection
set_option autoImplicit false
namespace NNH_MappedOk
open Aeneas Aeneas.Std AdapterRw NND_Carrier NNH_ModelCarrier
/-- Extract an actual native returned value from a successful carrier map. -/
theorem value {A B : Type} (f : A → B)
 (r : Result (core.result.Result A solana_program_error.ProgramError)) (b : B)
 (h : outer (reply f) r=.ok (.ok b)) :
 ∃ a,r=.ok (.Ok a) ∧ f a=b := by
 obtain ⟨a,ha,hb⟩ := NNH_MResultProjection.outer_ok (reply f) r (.ok b) h
 cases a with
 | Err e => cases hb
 | Ok a => exact ⟨a,ha,Except.ok.inj hb⟩
#print axioms value
end NNH_MappedOk
