import NEU_CommonProjections
set_option autoImplicit false
noncomputable section
namespace NFD_CommonField11
open Aeneas Aeneas.Std NEU_ReconstructCore
open NEU_PublicProjections (get)
def expected (a : Auth) (c : Candidate) (i : Fin 8) (j : Fin 32) (k : Fin 20) : Nat :=
  (get (get a.live_snapshot.frontier k) i).val
theorem alignment (a : Auth) (c : Candidate) (i : Fin 8) (j : Fin 32) (k : Fin 20) :
    NEU_CommonProjections.value (common a c) ⟨11,by decide⟩ i j k = expected a c i j k := rfl
#print axioms alignment
end NFD_CommonField11
