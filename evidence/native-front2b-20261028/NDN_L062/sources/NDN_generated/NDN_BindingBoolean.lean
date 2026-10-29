import NDN_Reference17.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDN_BindingBoolean

theorem matches (kind master lane output nullifier after : Bool) :
 NDN_Reference17.binding_matches kind master lane output nullifier after=
 ok (kind && master && lane && output && nullifier && after) := by
 cases kind <;> cases master <;> cases lane <;> cases output <;> cases nullifier <;> cases after <;> rfl

theorem accepted (kind master lane output nullifier after : Bool)
 (h:NDN_Reference17.binding_matches kind master lane output nullifier after=ok true) :
 kind=true ∧ master=true ∧ lane=true ∧ output=true ∧ nullifier=true ∧ after=true := by
 rw [matches] at h
 have h' := Result.ok.inj h
 simpa only [Bool.and_eq_true] using h'

#print axioms matches
#print axioms accepted
end NDN_BindingBoolean
