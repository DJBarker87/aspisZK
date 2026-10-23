import ExtractedCurrentM31AddSub
import ExtractedMaskCM31Square
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9CheckedProbeSelectedWordsV1

theorem m31_add_same (x y : Std.U32) :
    AspisR1Qm31ArithmeticProbe.field.M31.add x y =
      AspisR1SelectedMaskProbe.field.M31.add x y := by
  unfold AspisR1Qm31ArithmeticProbe.field.M31.add
    AspisR1SelectedMaskProbe.field.M31.add
    AspisR1Qm31ArithmeticProbe.field.P AspisR1SelectedMaskProbe.field.P
  rfl

theorem m31_sub_same (x y : Std.U32) :
    AspisR1Qm31ArithmeticProbe.field.M31.sub x y =
      AspisR1SelectedMaskProbe.field.M31.sub x y := by
  unfold AspisR1Qm31ArithmeticProbe.field.M31.sub
    AspisR1SelectedMaskProbe.field.M31.sub
    AspisR1Qm31ArithmeticProbe.field.P AspisR1SelectedMaskProbe.field.P
  rfl

theorem reduce_same (x : Std.U64) :
    AspisR1Qm31ArithmeticProbe.field.reduce_u64 x =
      AspisR1SelectedMaskProbe.field.reduce_u64 x := by
  unfold AspisR1Qm31ArithmeticProbe.field.reduce_u64
    AspisR1SelectedMaskProbe.field.reduce_u64
    AspisR1Qm31ArithmeticProbe.field.P AspisR1SelectedMaskProbe.field.P
  rfl

theorem m31_reduce_same (x : Std.U64) :
    AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64 x =
      AspisR1SelectedMaskProbe.field.M31.reduce_u64 x := by
  unfold AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64
    AspisR1SelectedMaskProbe.field.M31.reduce_u64
  simp only [reduce_same]

theorem m31_mul_same (x y : Std.U32) :
    AspisR1Qm31ArithmeticProbe.field.M31.mul x y =
      AspisR1SelectedMaskProbe.field.M31.mul x y := by
  unfold AspisR1Qm31ArithmeticProbe.field.M31.mul
    AspisR1SelectedMaskProbe.field.M31.mul
  simp only [reduce_same]

theorem m31_double_same (x : Std.U32) :
    AspisR1Qm31ArithmeticProbe.field.M31.double x =
      AspisR1SelectedMaskProbe.field.M31.double x := by
  unfold AspisR1Qm31ArithmeticProbe.field.M31.double
    AspisR1SelectedMaskProbe.field.M31.double
  exact m31_add_same x x

#print axioms m31_add_same

#print axioms m31_sub_same

#print axioms reduce_same

#print axioms m31_reduce_same

#print axioms m31_mul_same

#print axioms m31_double_same

end AspisR1S9CheckedProbeSelectedWordsV1
