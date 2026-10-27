import FJe_RawReference
set_option autoImplicit false
namespace AspisR1.FJe_RawSafety0
/-- Every intermediate of reference raw component0 is safe in source order.
The bound is the native 7P; it remains symbolic in this arithmetic lemma. -/
theorem value (b : Nat) (w : Fin 4 → Fin 4 → Nat)
    (hw : ∀ r j,w r j<b) :
    w 1 1≤w 0 0+5*b ∧
    w 0 0+5*b<8*b ∧
    w 2 3≤w 0 0+5*b-w 1 1+2*w 2 2 ∧
    w 0 0+5*b-w 1 1+2*w 2 2<8*b ∧
    w 3 2≤w 0 0+5*b-w 1 1+2*w 2 2-w 2 3 ∧
    2*w 3 3≤w 0 0+5*b-w 1 1+2*w 2 2-w 2 3-w 3 2 ∧
    w 0 0+5*b-w 1 1+2*w 2 2-w 2 3-w 3 2-2*w 3 3<8*b := by
  have h00 := hw 0 0
  have h11 := hw 1 1
  have h22 := hw 2 2
  have h23 := hw 2 3
  have h32 := hw 3 2
  have h33 := hw 3 3
  repeat' constructor <;> omega
#print axioms value
end AspisR1.FJe_RawSafety0
