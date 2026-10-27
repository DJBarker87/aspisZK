import FJe_RawReference
set_option autoImplicit false
namespace AspisR1.FJe_RawSafety2
/-- Exact source-order safety for raw component2. -/
theorem value (b : Nat) (w : Fin 4 → Fin 4 → Nat)
    (hw : ∀ r j,w r j<b) :
    w 0 2+2*b<4*b ∧
    w 1 3≤w 0 2+2*b ∧
    w 0 2+2*b-w 1 3+w 2 0<4*b ∧
    w 3 1≤w 0 2+2*b-w 1 3+w 2 0 ∧
    w 0 2+2*b-w 1 3+w 2 0-w 3 1<4*b := by
  have h02 := hw 0 2
  have h13 := hw 1 3
  have h20 := hw 2 0
  have h31 := hw 3 1
  repeat' constructor <;> omega
#print axioms value
end AspisR1.FJe_RawSafety2
