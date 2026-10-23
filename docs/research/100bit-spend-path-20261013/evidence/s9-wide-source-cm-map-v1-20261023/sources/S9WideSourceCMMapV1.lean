import AspisR1S9ActualWideMulCutV1.Funs
import AspisR1S9ActualQMMulCutV1.Funs
import S9WideSourcePrimitiveBridgeV1
import S9WideSourceRecordMapV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9WideSourceCMMapV1

abbrev WideCM := AspisR1S9ActualWideMulCutV1.field.CM31
abbrev QCM := AspisR1S9ActualQMMulCutV1.field.CM31

def mapResult {A B : Type} (f : A → B) : Result A → Result B
  | .ok x => .ok (f x)
  | .fail e => .fail e
  | .div => .div

def toQCM := AspisR1S9WideSourceRecordMapV1.toQCM

private theorem mapResult_ok {A B : Type} (f : A → B) (x : A) :
    mapResult f (.ok x) = .ok (f x) := rfl

private theorem mapResult_bind {A B C : Type} (f : A → B)
    (m : Result C) (k : C → Result A) :
    mapResult f (do let x ← m; k x) = (do let x ← m; mapResult f (k x)) := by
  cases m <;> rfl

theorem m31_reduce_u64_maps (x : Std.U64) :
    AspisR1S9ActualWideMulCutV1.field.M31.reduce_u64 x =
      AspisR1S9ActualQMMulCutV1.field.M31.reduce_u64 x := by
  unfold AspisR1S9ActualWideMulCutV1.field.M31.reduce_u64
    AspisR1S9ActualQMMulCutV1.field.M31.reduce_u64
  rw [AspisR1S9WideSourcePrimitiveBridgeV1.wide_reduce_u64_eq_qcut]

theorem cm_add_maps (x y : WideCM) :
    mapResult toQCM (AspisR1S9ActualWideMulCutV1.field.CM31.add x y) =
      AspisR1S9ActualQMMulCutV1.field.CM31.add (toQCM x) (toQCM y) := by
  simp only [AspisR1S9ActualWideMulCutV1.field.CM31.add,
    AspisR1S9ActualQMMulCutV1.field.CM31.add, mapResult_bind,
    AspisR1S9WideSourcePrimitiveBridgeV1.wide_m31_add_eq_qcut,
    mapResult_ok, toQCM, AspisR1S9WideSourceRecordMapV1.toQCM]

theorem cm_sub_maps (x y : WideCM) :
    mapResult toQCM (AspisR1S9ActualWideMulCutV1.field.CM31.sub x y) =
      AspisR1S9ActualQMMulCutV1.field.CM31.sub (toQCM x) (toQCM y) := by
  simp only [AspisR1S9ActualWideMulCutV1.field.CM31.sub,
    AspisR1S9ActualQMMulCutV1.field.CM31.sub, mapResult_bind,
    AspisR1S9WideSourcePrimitiveBridgeV1.wide_m31_sub_eq_qcut,
    mapResult_ok, toQCM, AspisR1S9WideSourceRecordMapV1.toQCM]

theorem cm_mul_maps (x y : WideCM) :
    mapResult toQCM (AspisR1S9ActualWideMulCutV1.field.CM31.mul x y) =
      AspisR1S9ActualQMMulCutV1.field.CM31.mul (toQCM x) (toQCM y) := by
  simp only [AspisR1S9ActualWideMulCutV1.field.CM31.mul,
    AspisR1S9ActualQMMulCutV1.field.CM31.mul, mapResult_bind,
    AspisR1S9WideSourcePrimitiveBridgeV1.wide_m31_mul_eq_qcut,
    m31_reduce_u64_maps,
    AspisR1S9WideSourcePrimitiveBridgeV1.wide_m31_sub_eq_qcut,
    mapResult_ok, toQCM, AspisR1S9WideSourceRecordMapV1.toQCM]

#print axioms m31_reduce_u64_maps
#print axioms cm_add_maps
#print axioms cm_sub_maps
#print axioms cm_mul_maps

end AspisR1S9WideSourceCMMapV1
