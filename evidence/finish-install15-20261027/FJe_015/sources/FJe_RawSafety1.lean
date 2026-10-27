import FJe_RawReference
set_option autoImplicit false
namespace AspisR1.FJe_RawSafety1
/-- Every growing prefix and the final subtraction of raw component1. -/
theorem value (b : Nat) (w : Fin 4 → Fin 4 → Nat)
    (hw : ∀ r j,w r j<b) :
    w 0 1+w 1 0<8*b ∧
    w 0 1+w 1 0+w 2 2<8*b ∧
    w 0 1+w 1 0+w 2 2+2*w 2 3<8*b ∧
    w 0 1+w 1 0+w 2 2+2*w 2 3+2*w 3 2<8*b ∧
    w 0 1+w 1 0+w 2 2+2*w 2 3+2*w 3 2+b<8*b ∧
    w 3 3≤w 0 1+w 1 0+w 2 2+2*w 2 3+2*w 3 2+b ∧
    w 0 1+w 1 0+w 2 2+2*w 2 3+2*w 3 2+b-w 3 3<8*b := by
  have h01 := hw 0 1
  have h10 := hw 1 0
  have h22 := hw 2 2
  have h23 := hw 2 3
  have h32 := hw 3 2
  have h33 := hw 3 3
  repeat' constructor <;> omega
#print axioms value
end AspisR1.FJe_RawSafety1
