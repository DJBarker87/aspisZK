import NEI_ReplayFieldArithmetic
set_option autoImplicit false
namespace NEI_ProfilePair
open Aeneas Aeneas.Std Result AspisR1
open NEI_FIo_FieldBridge (NQ NE qm wide map)
/-- Symbolic two-child record transport: no concrete field definition unfolds. -/
theorem wide_pair (a b : Result NQ) :
    map wide (do let x ← a; let y ← b; ok (⟨x,y⟩ : NE)) =
      (do let x ← map qm a; let y ← map qm b;
          ok (⟨x,y⟩ : AspisR1CurrentWide.field.wide_exact.WideExact)) := by
  cases a <;> cases b <;> rfl
#print axioms wide_pair
end NEI_ProfilePair
