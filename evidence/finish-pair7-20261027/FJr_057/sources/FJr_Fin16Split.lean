import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Abel
set_option autoImplicit false
namespace AspisR1.FJr_Fin16Split
open scoped BigOperators

theorem value {E : Type} [AddCommMonoid E] (f : Fin 16 → E) :
    (∑ j : Fin 16,f j)=∑ s : Fin 4,∑ t : Fin 4,f ⟨4*s.val+t.val,by have:=s.isLt;have:=t.isLt;omega⟩ := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.val_zero,Fin.val_succ,add_zero]
  ac_rfl

#print axioms value
end AspisR1.FJr_Fin16Split
