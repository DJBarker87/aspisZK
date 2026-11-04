import NEU_CommonProjections
set_option autoImplicit false
noncomputable section
namespace NFD_CommonField12
open Aeneas Aeneas.Std NEU_ReconstructCore
open NEU_PublicProjections (get)
def expected (a : Auth) (c : Candidate) (i : Fin 8) (j : Fin 32) (k : Fin 20) : Nat :=
  c.next_pair_index.val
theorem alignment (a : Auth) (c : Candidate) (i : Fin 8) (j : Fin 32) (k : Fin 20) :
    NEU_CommonProjections.value (common a c) ⟨12,by decide⟩ i j k = expected a c i j k := rfl
#print axioms alignment
end NFD_CommonField12
