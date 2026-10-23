import S9CheckedProbeSelectedWordsV1
import S9SourceResultTransportV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9CheckedProbeSelectedCMV1
abbrev ProbeCM := AspisR1Qm31ArithmeticProbe.field.CM31
abbrev SelectedCM := AspisR1SelectedMaskProbe.field.CM31

def toSelectedCM (x : ProbeCM) : SelectedCM := ⟨x.a,x.b⟩
abbrev mapResult {A B : Type} (f : A → B) (r : Result A) :=
  AspisR1S9SourceResultTransportV1.mapResult f r

private theorem map_bind {A B C : Type} (f:B→C) (r:Result A) (k:A→Result B) :
    mapResult f (r >>= k) = (r >>= fun x => mapResult f (k x)) := by
  cases r <;> rfl
private theorem map_ok {A B : Type} (f:A→B) (x:A) : mapResult f (.ok x) = .ok (f x) := rfl

theorem cm_add_maps (x y : ProbeCM) :
    mapResult toSelectedCM (AspisR1Qm31ArithmeticProbe.field.CM31.add x y) =
      AspisR1SelectedMaskProbe.field.CM31.add (toSelectedCM x) (toSelectedCM y) := by
  simp only [AspisR1Qm31ArithmeticProbe.field.CM31.add,
    AspisR1SelectedMaskProbe.field.CM31.add, map_bind,
    AspisR1S9CheckedProbeSelectedWordsV1.m31_add_same,
    AspisR1S9CheckedProbeSelectedWordsV1.m31_sub_same,
    AspisR1S9CheckedProbeSelectedWordsV1.m31_mul_same,
    AspisR1S9CheckedProbeSelectedWordsV1.m31_reduce_same,
    map_ok, toSelectedCM]

theorem cm_sub_maps (x y : ProbeCM) :
    mapResult toSelectedCM (AspisR1Qm31ArithmeticProbe.field.CM31.sub x y) =
      AspisR1SelectedMaskProbe.field.CM31.sub (toSelectedCM x) (toSelectedCM y) := by
  simp only [AspisR1Qm31ArithmeticProbe.field.CM31.sub,
    AspisR1SelectedMaskProbe.field.CM31.sub, map_bind,
    AspisR1S9CheckedProbeSelectedWordsV1.m31_add_same,
    AspisR1S9CheckedProbeSelectedWordsV1.m31_sub_same,
    AspisR1S9CheckedProbeSelectedWordsV1.m31_mul_same,
    AspisR1S9CheckedProbeSelectedWordsV1.m31_reduce_same,
    map_ok, toSelectedCM]

theorem cm_mul_maps (x y : ProbeCM) :
    mapResult toSelectedCM (AspisR1Qm31ArithmeticProbe.field.CM31.mul x y) =
      AspisR1SelectedMaskProbe.field.CM31.mul (toSelectedCM x) (toSelectedCM y) := by
  simp only [AspisR1Qm31ArithmeticProbe.field.CM31.mul,
    AspisR1SelectedMaskProbe.field.CM31.mul, map_bind,
    AspisR1S9CheckedProbeSelectedWordsV1.m31_add_same,
    AspisR1S9CheckedProbeSelectedWordsV1.m31_sub_same,
    AspisR1S9CheckedProbeSelectedWordsV1.m31_mul_same,
    AspisR1S9CheckedProbeSelectedWordsV1.m31_reduce_same,
    map_ok, toSelectedCM]

theorem by_r_maps (x : ProbeCM) :
    mapResult toSelectedCM (AspisR1Qm31ArithmeticProbe.field.mul_by_r x) =
      AspisR1SelectedMaskProbe.field.mul_by_r (toSelectedCM x) := by
  simp only [AspisR1Qm31ArithmeticProbe.field.mul_by_r,
    AspisR1SelectedMaskProbe.field.mul_by_r, map_bind,
    AspisR1S9CheckedProbeSelectedWordsV1.m31_double_same,
    AspisR1S9CheckedProbeSelectedWordsV1.m31_sub_same,
    AspisR1S9CheckedProbeSelectedWordsV1.m31_add_same,
    map_ok,toSelectedCM]

theorem cm_add_self_maps_double (x : ProbeCM) :
    mapResult toSelectedCM (AspisR1Qm31ArithmeticProbe.field.CM31.add x x) =
      AspisR1SelectedMaskProbe.field.CM31.double (toSelectedCM x) := by
  unfold AspisR1SelectedMaskProbe.field.CM31.double
  exact cm_add_maps x x

#print axioms cm_add_maps

#print axioms cm_sub_maps

#print axioms cm_mul_maps

#print axioms by_r_maps

#print axioms cm_add_self_maps_double

end AspisR1S9CheckedProbeSelectedCMV1
