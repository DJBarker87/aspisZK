import AspisR1S9SquareMulQMCutV1.Funs
import AspisR1S9ActualQMMulCutV1.Funs
import S9SourceResultTransportV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9QMSquareMixedProductMapV1

def mapActualCM (x : AspisR1S9SquareMulQMCutV1.field.CM31) :
    AspisR1S9ActualQMMulCutV1.field.CM31 := ⟨x.a, x.b⟩

abbrev mapResult {A B : Type} (f : A → B) : Result A → Result B :=
  AspisR1S9SourceResultTransportV1.mapResult f

private theorem mapResult_ok {A B : Type} (f : A → B) (x : A) :
    mapResult f (.ok x) = .ok (f x) := rfl

private theorem mapResult_bind {A B C : Type} (f : B → C) (r : Result A)
    (k : A → Result B) :
    mapResult f (Bind.bind r k) = Bind.bind r (fun x => mapResult f (k x)) := by
  cases r <;> rfl

theorem m31_add_same (x y : AspisR1S9SquareMulQMCutV1.field.M31) :
    AspisR1S9SquareMulQMCutV1.field.M31.add x y =
      AspisR1S9ActualQMMulCutV1.field.M31.add x y := by
  unfold AspisR1S9SquareMulQMCutV1.field.M31.add
    AspisR1S9ActualQMMulCutV1.field.M31.add
    AspisR1S9SquareMulQMCutV1.field.P AspisR1S9ActualQMMulCutV1.field.P
  rfl

theorem m31_sub_same (x y : AspisR1S9SquareMulQMCutV1.field.M31) :
    AspisR1S9SquareMulQMCutV1.field.M31.sub x y =
      AspisR1S9ActualQMMulCutV1.field.M31.sub x y := by
  unfold AspisR1S9SquareMulQMCutV1.field.M31.sub
    AspisR1S9ActualQMMulCutV1.field.M31.sub
    AspisR1S9SquareMulQMCutV1.field.P AspisR1S9ActualQMMulCutV1.field.P
  rfl

theorem field_reduce_u64_same (x : Std.U64) :
    AspisR1S9SquareMulQMCutV1.field.reduce_u64 x =
      AspisR1S9ActualQMMulCutV1.field.reduce_u64 x := by
  unfold AspisR1S9SquareMulQMCutV1.field.reduce_u64
    AspisR1S9ActualQMMulCutV1.field.reduce_u64
    AspisR1S9SquareMulQMCutV1.field.P
    AspisR1S9ActualQMMulCutV1.field.P
  rfl

theorem method_reduce_u64_same (x : Std.U64) :
    AspisR1S9SquareMulQMCutV1.field.M31.reduce_u64 x =
      AspisR1S9ActualQMMulCutV1.field.M31.reduce_u64 x := by
  unfold AspisR1S9SquareMulQMCutV1.field.M31.reduce_u64
    AspisR1S9ActualQMMulCutV1.field.M31.reduce_u64
  simp only [field_reduce_u64_same]

theorem m31_mul_same (x y : AspisR1S9SquareMulQMCutV1.field.M31) :
    AspisR1S9SquareMulQMCutV1.field.M31.mul x y =
      AspisR1S9ActualQMMulCutV1.field.M31.mul x y := by
  unfold AspisR1S9SquareMulQMCutV1.field.M31.mul
    AspisR1S9ActualQMMulCutV1.field.M31.mul
  simp only [field_reduce_u64_same]

theorem m31_double_same (x : AspisR1S9SquareMulQMCutV1.field.M31) :
    AspisR1S9SquareMulQMCutV1.field.M31.double x =
      AspisR1S9ActualQMMulCutV1.field.M31.double x := by
  unfold AspisR1S9SquareMulQMCutV1.field.M31.double
    AspisR1S9ActualQMMulCutV1.field.M31.double
  exact m31_add_same x x

theorem cm_add_map (x y : AspisR1S9SquareMulQMCutV1.field.CM31) :
    mapResult mapActualCM (AspisR1S9SquareMulQMCutV1.field.CM31.add x y) =
      AspisR1S9ActualQMMulCutV1.field.CM31.add (mapActualCM x) (mapActualCM y) := by
  unfold AspisR1S9SquareMulQMCutV1.field.CM31.add
    AspisR1S9ActualQMMulCutV1.field.CM31.add
  simp only [mapResult_bind, m31_add_same, mapResult_ok, mapActualCM]

theorem cm_sub_map (x y : AspisR1S9SquareMulQMCutV1.field.CM31) :
    mapResult mapActualCM (AspisR1S9SquareMulQMCutV1.field.CM31.sub x y) =
      AspisR1S9ActualQMMulCutV1.field.CM31.sub (mapActualCM x) (mapActualCM y) := by
  unfold AspisR1S9SquareMulQMCutV1.field.CM31.sub
    AspisR1S9ActualQMMulCutV1.field.CM31.sub
  simp only [mapResult_bind, m31_sub_same, mapResult_ok, mapActualCM]

theorem cm_mul_map (x y : AspisR1S9SquareMulQMCutV1.field.CM31) :
    mapResult mapActualCM (AspisR1S9SquareMulQMCutV1.field.CM31.mul x y) =
      AspisR1S9ActualQMMulCutV1.field.CM31.mul (mapActualCM x) (mapActualCM y) := by
  unfold AspisR1S9SquareMulQMCutV1.field.CM31.mul
    AspisR1S9ActualQMMulCutV1.field.CM31.mul
  simp only [mapResult_bind, m31_mul_same, m31_add_same, m31_sub_same,
    m31_double_same, method_reduce_u64_same, mapResult_ok, mapActualCM]

#print axioms m31_add_same
#print axioms m31_sub_same
#print axioms field_reduce_u64_same
#print axioms method_reduce_u64_same
#print axioms m31_mul_same
#print axioms m31_double_same
#print axioms cm_add_map
#print axioms cm_sub_map
#print axioms cm_mul_map

end AspisR1S9QMSquareMixedProductMapV1
