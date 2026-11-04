import NFD_RequestProjection
set_option autoImplicit false
noncomputable section
namespace NFD_RequestField00
open Aeneas Aeneas.Std NFD_RequestProjection
open NEU_PublicProjections (get)
def expected (s : Request) (i : Fin 8) (j : Fin 32) : Nat :=
 (get s.verifier_profile j).val
theorem alignment (s : Request) (i : Fin 8) (j : Fin 32) :
    project s ⟨0,by decide⟩ i j=expected s i j := by
  rfl

#print axioms alignment
end NFD_RequestField00
