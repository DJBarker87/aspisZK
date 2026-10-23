import CurrentWideBaseBridge
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentWide.Proof

/-- Exact checked subtraction body map to the two checked Probe CM calls. -/
theorem qm_sub_same_wide (x y : field.QM31) :
    (do let z ← field.QM31.sub x y; ok (toQM z)) =
      (do
        let a ← AspisR1Qm31ArithmeticProbe.field.CM31.sub
          (toCM x.c0) (toCM y.c0)
        let b ← AspisR1Qm31ArithmeticProbe.field.CM31.sub
          (toCM x.c1) (toCM y.c1)
        ok (⟨a, b⟩ : AspisR1Qm31ArithmeticProbe.field.QM31)) := by
  unfold field.QM31.sub
  simp only [toQM, ←cm_sub_same, bind_assoc_eq, bind_tc_ok]

#print axioms qm_sub_same_wide
end AspisR1CurrentWide.Proof
