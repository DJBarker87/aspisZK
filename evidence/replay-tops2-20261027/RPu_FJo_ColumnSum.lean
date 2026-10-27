import RPu_FJo_Sum29
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_ColumnSum
open scoped BigOperators
/-- Abstract algebraic 29-column transport, independent of concrete field encoding. -/
theorem value {E : Type} [CommSemiring E] (g : E) (w : Fin 29 → E)
    (b : Nat → E) (t0 t1 t2 : E)
    (base : ∀ l : Fin 26,w ⟨l.val,by have:=l.isLt;omega⟩=b l.val)
    (h0 : w 28=t0) (h1 : w 26=t1) (h2 : w 27=t2) :
    (∑ l : Fin 29,w l*g^l.val)=(∑ l ∈ Finset.range 26,g^l*b l)+
      (g^28*t0+g^26*t1+g^27*t2) := by
  simp only [mul_comm (w _) _]
  rw [FJo_Sum29.split,h0,h1,h2]
  congr 1
  rw [←Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro l hl
  rw [base l]
#print axioms value
end AspisR1.FJo_ColumnSum
end
