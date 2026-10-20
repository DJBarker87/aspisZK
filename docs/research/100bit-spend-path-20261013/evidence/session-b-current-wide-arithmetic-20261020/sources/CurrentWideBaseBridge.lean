import AspisR1CurrentWide.Funs
import R17CurrentM31Semantics
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentWide.Proof
namespace Old
abbrev M31 := AspisR1Qm31ArithmeticProbe.field.M31
abbrev CM31 := AspisR1Qm31ArithmeticProbe.field.CM31
abbrev QM31 := AspisR1Qm31ArithmeticProbe.field.QM31
end Old

def toCM (x : field.CM31) : Old.CM31 := ⟨x.a,x.b⟩
def toQM (x : field.QM31) : Old.QM31 := ⟨toCM x.c0,toCM x.c1⟩

theorem m31_add_same : field.M31.add = AspisR1Qm31ArithmeticProbe.field.M31.add := by
  funext x y
  unfold field.M31.add AspisR1Qm31ArithmeticProbe.field.M31.add field.P AspisR1Qm31ArithmeticProbe.field.P
  rfl

theorem m31_sub_same : field.M31.sub = AspisR1Qm31ArithmeticProbe.field.M31.sub := by
  funext x y
  unfold field.M31.sub AspisR1Qm31ArithmeticProbe.field.M31.sub field.P AspisR1Qm31ArithmeticProbe.field.P
  rfl

theorem reduce_same : field.reduce_u64 = AspisR1Qm31ArithmeticProbe.field.reduce_u64 := by
  funext x
  unfold field.reduce_u64 AspisR1Qm31ArithmeticProbe.field.reduce_u64 field.P AspisR1Qm31ArithmeticProbe.field.P
  rfl

theorem m31_mul_same : field.M31.mul = AspisR1Qm31ArithmeticProbe.field.M31.mul := by
  funext x y
  unfold field.M31.mul AspisR1Qm31ArithmeticProbe.field.M31.mul
  rw [reduce_same]

theorem m31_reduce_same : field.M31.reduce_u64 = AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64 := by
  funext x
  unfold field.M31.reduce_u64 AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64
  rw [reduce_same]

theorem m31_double_same : field.M31.double = AspisR1Qm31ArithmeticProbe.field.M31.double := by
  funext x
  unfold field.M31.double AspisR1Qm31ArithmeticProbe.field.M31.double
  rw [m31_add_same]

theorem cm_add_same (x y : field.CM31) :
    (do let z ← field.CM31.add x y; ok (toCM z)) =
      AspisR1Qm31ArithmeticProbe.field.CM31.add (toCM x) (toCM y) := by
  unfold field.CM31.add AspisR1Qm31ArithmeticProbe.field.CM31.add
  simp only [bind_assoc_eq,bind_tc_ok,m31_add_same,toCM]

theorem cm_sub_same (x y : field.CM31) :
    (do let z ← field.CM31.sub x y; ok (toCM z)) =
      AspisR1Qm31ArithmeticProbe.field.CM31.sub (toCM x) (toCM y) := by
  unfold field.CM31.sub AspisR1Qm31ArithmeticProbe.field.CM31.sub
  simp only [bind_assoc_eq,bind_tc_ok,m31_sub_same,toCM]

theorem cm_mul_same (x y : field.CM31) :
    (do let z ← field.CM31.mul x y; ok (toCM z)) =
      AspisR1Qm31ArithmeticProbe.field.CM31.mul (toCM x) (toCM y) := by
  unfold field.CM31.mul AspisR1Qm31ArithmeticProbe.field.CM31.mul
  simp only [bind_assoc_eq,bind_tc_ok,m31_mul_same,m31_reduce_same,m31_sub_same,toCM]

theorem mul_by_r_same (x : field.CM31) :
    (do let z ← field.mul_by_r x; ok (toCM z)) =
      AspisR1Qm31ArithmeticProbe.field.mul_by_r (toCM x) := by
  unfold field.mul_by_r AspisR1Qm31ArithmeticProbe.field.mul_by_r
  simp only [bind_assoc_eq,bind_tc_ok,m31_double_same,m31_add_same,m31_sub_same,toCM]

#print axioms m31_add_same
#print axioms m31_sub_same
#print axioms reduce_same
#print axioms m31_mul_same
#print axioms m31_reduce_same
#print axioms m31_double_same
#print axioms cm_add_same
#print axioms cm_sub_same
#print axioms cm_mul_same
#print axioms mul_by_r_same
end AspisR1CurrentWide.Proof
