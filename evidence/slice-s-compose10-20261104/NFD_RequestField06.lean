import NFD_RequestProjection
set_option autoImplicit false
noncomputable section
namespace NFD_RequestField06
open Aeneas Aeneas.Std NFD_RequestProjection
open NEU_PublicProjections (get)
def expected (s : Request) (i : Fin 8) (j : Fin 32) : Nat :=
 match s.«public» with
 | .PrivateTransfer p => p.anchor_sequence.val
 | .Withdrawal p => p.anchor_sequence.val
theorem alignment (s : Request) (i : Fin 8) (j : Fin 32) :
    project s ⟨6,by decide⟩ i j=expected s i j := by
  cases h : s.«public» <;> simp only [project,expected,h] <;> rfl

#print axioms alignment
end NFD_RequestField06
