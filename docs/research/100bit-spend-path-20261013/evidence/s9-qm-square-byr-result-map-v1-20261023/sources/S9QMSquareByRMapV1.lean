import S9QMSquareMixedProductMapV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9QMSquareByRMapV1

abbrev CM := AspisR1S9SquareMulQMCutV1.field.CM31
abbrev ActualCM := AspisR1S9ActualQMMulCutV1.field.CM31

def mapCM (x : CM) : ActualCM := ⟨x.a, x.b⟩

private abbrev mapResult {A B : Type} (f : A → B) : Result A → Result B :=
  AspisR1S9QMSquareMixedProductMapV1.mapResult f

private theorem mapResult_ok {A B : Type} (f : A → B) (x : A) :
    mapResult f (.ok x) = .ok (f x) := rfl

private theorem mapResult_bind {A B C : Type} (f : B → C) (r : Result A)
    (k : A → Result B) :
    mapResult f (Bind.bind r k) = Bind.bind r (fun x => mapResult f (k x)) := by
  cases r <;> rfl

/-- The `mul_by_r` source body in the combined square cut maps structurally to
its source body in the actual QM multiplication cut. -/
theorem by_r_maps_to_actual (x : CM) :
    mapResult mapCM (AspisR1S9SquareMulQMCutV1.field.mul_by_r x) =
      AspisR1S9ActualQMMulCutV1.field.mul_by_r (mapCM x) := by
  unfold AspisR1S9SquareMulQMCutV1.field.mul_by_r AspisR1S9ActualQMMulCutV1.field.mul_by_r
  simp only [mapResult_bind,
    AspisR1S9QMSquareMixedProductMapV1.m31_double_same,
    AspisR1S9QMSquareMixedProductMapV1.m31_sub_same,
    AspisR1S9QMSquareMixedProductMapV1.m31_add_same,
    mapResult_ok, mapCM]

#print axioms by_r_maps_to_actual

end AspisR1S9QMSquareByRMapV1
