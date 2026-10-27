import FJl_SlotLiteral
import FJl_WordTails
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_Sum29
open scoped BigOperators
/-- Symbolic partition of the 29 terms. No field numeral normalization. -/
theorem split {E : Type} [AddCommMonoid E] (f : Fin 29 → E) :
    (∑ l : Fin 29,f l)=(∑ l : Fin 26,f ⟨l.val,by have:=l.isLt;omega⟩)+
      (f 28+f 26+f 27) := by
  have h := Fin.sum_univ_add f (a:=26) (b:=3)
  rw [h]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,Fin.castAdd,Fin.natAdd,Fin.val_zero,Fin.val_succ]
  ac_rfl
#print axioms split
end AspisR1.FJo_Sum29
end
