import NFD_RequestProjection
set_option autoImplicit false
noncomputable section
namespace NFD_RequestField12
open Aeneas Aeneas.Std NFD_RequestProjection
open NEU_PublicProjections (get)
def expected (s : Request) (i : Fin 8) (j : Fin 32) : Nat :=
 match s.«public» with
 | .PrivateTransfer p => 0
 | .Withdrawal p => p.amount.val
theorem alignment (s : Request) (i : Fin 8) (j : Fin 32) :
    project s ⟨12,by decide⟩ i j=expected s i j := by
  cases h : s.«public» <;> simp only [project,expected,h] <;> rfl

#print axioms alignment
end NFD_RequestField12
