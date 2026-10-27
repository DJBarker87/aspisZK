import FJm_LibraModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_SparseDot
open scoped BigOperators

theorem value {E : Type} [Field E] (f : Fin 64 → E) (q0 q1 a0 a1 : E) :
    RoundPairing.dot f (FJm_LibraModel.folded q0 q1 a0 a1)=
      ∑ j : Fin 4,f ⟨j.val,by have:=j.isLt;omega⟩*FJm_LibraModel.part q0 q1 a0 a1 j := by
  unfold RoundPairing.dot
  rw [Fin.sum_univ_add (a:=4) (b:=60)]
  have tail : (∑ j : Fin 60,f (Fin.natAdd 4 j)*
      FJm_LibraModel.folded q0 q1 a0 a1 (Fin.natAdd 4 j))=0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [FJm_LibraModel.support q0 q1 a0 a1 _ (by simp only [Fin.val_natAdd];omega),mul_zero]
  rw [tail,add_zero]
  apply Finset.sum_congr rfl
  intro j _
  rw [FJm_LibraModel.small]

#print axioms value
end AspisR1.FJr_SparseDot
end
