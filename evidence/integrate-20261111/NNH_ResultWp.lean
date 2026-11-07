import NNH_ValidateFission
set_option autoImplicit false
namespace NNH_ResultWp
open Aeneas Aeneas.Std Result

theorem expose {A : Type} (raw : Result A) (P : A → Prop)
 (proof : raw ⦃x => P x⦄) : ∃ x,raw=.ok x ∧ P x := by
 cases raw with
 | fail e => cases proof
 | div => cases proof
 | ok x => exact ⟨x,rfl,proof⟩
#print axioms expose
end NNH_ResultWp
