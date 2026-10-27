import FJe_RawReference
set_option autoImplicit false
namespace AspisR1.FJe_RawSafety3
/-- Exact growing-prefix bounds for raw component3. -/
theorem value (b : Nat) (w : Fin 4 → Fin 4 → Nat)
    (hw : ∀ r j,w r j<b) :
    w 0 3+w 1 2<4*b ∧
    w 0 3+w 1 2+w 2 1<4*b ∧
    w 0 3+w 1 2+w 2 1+w 3 0<4*b := by
  have h03 := hw 0 3
  have h12 := hw 1 2
  have h21 := hw 2 1
  have h30 := hw 3 0
  repeat' constructor <;> omega
#print axioms value
end AspisR1.FJe_RawSafety3
