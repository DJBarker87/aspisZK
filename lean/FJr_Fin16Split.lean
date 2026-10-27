import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Abel
set_option autoImplicit false
namespace AspisR1.FJr_Fin16Split
open scoped BigOperators

theorem value {E : Type} [AddCommMonoid E] (f : Fin 16 → E) :
    (∑ j : Fin 16,f j)=∑ s : Fin 4,∑ t : Fin 4,f ⟨4*s.val+t.val,by have:=s.isLt;have:=t.isLt;omega⟩ := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.val_zero,Fin.val_succ,add_zero]
  change (f 0+(f 1+(f 2+(f 3+(f 4+(f 5+(f 6+(f 7+(f 8+(f 9+(f 10+(f 11+(f 12+(f 13+(f 14+f 15)))))))))))))))=((f 0+(f 1+(f 2+f 3)))+((f 4+(f 5+(f 6+f 7)))+((f 8+(f 9+(f 10+f 11)))+(f 12+(f 13+(f 14+f 15))))))
  ac_rfl

#print axioms value
end AspisR1.FJr_Fin16Split
