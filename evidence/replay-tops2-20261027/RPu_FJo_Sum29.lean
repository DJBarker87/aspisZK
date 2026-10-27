import RPu_FJl_SlotLiteral
import RPu_FJl_WordTails
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_Sum29
open scoped BigOperators
/-- Symbolic partition of the 29 terms. No field numeral normalization. -/
theorem split {E : Type} [AddCommMonoid E] (f : Fin 29 → E) :
    (∑ l : Fin 29,f l)=(∑ l : Fin 26,f ⟨l.val,by have:=l.isLt;omega⟩)+
      (f 28+f 26+f 27) := by
  rw [Fin.sum_univ_add (a:=26) (b:=3)]
  have tail : (∑ j : Fin 3,f (Fin.natAdd 26 j))=f 28+f 26+f 27 := by
    rw [Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ]
    simp only [Fin.sum_univ_zero,add_zero]
    change f 26+(f 27+f 28)=f 28+f 26+f 27
    ac_rfl
  rw [tail]
  rfl
#print axioms split
end AspisR1.FJo_Sum29
end
