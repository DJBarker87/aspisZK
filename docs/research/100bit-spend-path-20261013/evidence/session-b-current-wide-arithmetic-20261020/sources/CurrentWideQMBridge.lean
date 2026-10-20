import CurrentWideBaseBridge
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentWide.Proof

theorem qm_add_same (x y : field.QM31) :
    (do let z ← field.QM31.add x y; ok (toQM z)) =
      AspisR1Qm31ArithmeticProbe.field.QM31.add (toQM x) (toQM y) := by
  unfold field.QM31.add AspisR1Qm31ArithmeticProbe.field.QM31.add
  simp only [toQM,←cm_add_same,bind_assoc_eq,bind_tc_ok]

theorem qm_mul_same (x y : field.QM31) :
    (do let z ← field.QM31.mul x y; ok (toQM z)) =
      AspisR1Qm31ArithmeticProbe.field.QM31.mul (toQM x) (toQM y) := by
  unfold field.QM31.mul AspisR1Qm31ArithmeticProbe.field.QM31.mul
  simp only [toQM,←cm_mul_same,←cm_add_same,←cm_sub_same,←mul_by_r_same,bind_assoc_eq,bind_tc_ok]

#print axioms qm_add_same
#print axioms qm_mul_same
end AspisR1CurrentWide.Proof
