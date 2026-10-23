import AspisR1S9SquareMulQMCutV1.Funs
import S9QMSquareMixedProductMapV1
import S9QMSquareByRMapV1
import S9ActualQM31WrappingMapV1
import R22CanonicalCM31
import R22CanonicalQM31

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9QMSquareCombinedProbeOpsV1

abbrev SCM := AspisR1S9SquareMulQMCutV1.field.CM31
abbrev PCM := AspisR1Qm31ArithmeticProbe.field.CM31

def toProbe (x : SCM) : PCM := ⟨x.a, x.b⟩

abbrev toActual := AspisR1S9QMSquareMixedProductMapV1.mapActualCM
abbrev actualToProbe := AspisR1S9ActualQM31WrappingMapV1.toProbeCM
abbrev fromProbe := AspisR1S9ActualQM31WrappingMapV1.fromProbeCM
abbrev mapResult {A B : Type} (f : A → B) : Result A → Result B :=
  AspisR1S9SourceResultTransportV1.mapResult f

private theorem mapResult_comp {A B C : Type} (f : B → C) (g : A → B)
    (r : Result A) :
    mapResult f (mapResult g r) = mapResult (fun x => f (g x)) r := by
  cases r <;> rfl

private theorem actual_from_probe (x : PCM) :
    actualToProbe (fromProbe x) = x := by
  cases x <;> rfl

private theorem probe_of_actual_map (x : SCM) :
    actualToProbe (toActual x) = toProbe x := by
  cases x <;> rfl

private theorem probe_add_canonical (x y : SCM)
    (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalCM (toProbe x))
    (hy : AspisR1.ExtractedCurrentTowerAdd.CanonicalCM (toProbe y)) :
    AspisR1Qm31ArithmeticProbe.field.CM31.add (toProbe x) (toProbe y) =
      .ok (AspisR1.R22CanonicalCM31.wrappingCMAdd (toProbe x) (toProbe y)) :=
  AspisR1.R22CanonicalCM31.cm_add_agrees _ _ hx hy

private theorem probe_mul_canonical (x y : SCM)
    (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalCM (toProbe x))
    (hy : AspisR1.ExtractedCurrentTowerAdd.CanonicalCM (toProbe y)) :
    AspisR1Qm31ArithmeticProbe.field.CM31.mul (toProbe x) (toProbe y) =
      .ok (AspisR1.R22CanonicalCM31.wrappingCMMul (toProbe x) (toProbe y)) :=
  AspisR1.R22CanonicalCM31.cm_mul_agrees _ _ hx hy

private theorem probe_sub_canonical (x y : SCM)
    (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalCM (toProbe x))
    (hy : AspisR1.ExtractedCurrentTowerAdd.CanonicalCM (toProbe y)) :
    AspisR1Qm31ArithmeticProbe.field.CM31.sub (toProbe x) (toProbe y) =
      .ok (AspisR1.R22CanonicalCM31.wrappingCMSub (toProbe x) (toProbe y)) :=
  AspisR1.R22CanonicalCM31.cm_sub_agrees _ _ hx hy

/-- Combined-cut CM addition maps through the actual source-cut implementation
and its retained R22 checked/wrapping contract to the checked arithmetic probe.
Canonicality is required only for the checked Probe result. -/
theorem combined_cm_add_maps_to_probe (x y : SCM)
    (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalCM (toProbe x))
    (hy : AspisR1.ExtractedCurrentTowerAdd.CanonicalCM (toProbe y)) :
    mapResult toProbe (AspisR1S9SquareMulQMCutV1.field.CM31.add x y) =
      AspisR1Qm31ArithmeticProbe.field.CM31.add (toProbe x) (toProbe y) := by
  have hstruct := AspisR1S9QMSquareMixedProductMapV1.cm_add_map x y
  have hactual :
      mapResult actualToProbe
        (AspisR1S9ActualQMMulCutV1.field.CM31.add (toActual x) (toActual y)) =
      .ok (AspisR1.R22CanonicalCM31.wrappingCMAdd (toProbe x) (toProbe y)) := by
    rw [AspisR1S9ActualQM31WrappingMapV1.actual_cm_add_eq_ok]
    simp only [mapResult, AspisR1S9SourceResultTransportV1.mapResult, probe_of_actual_map, actual_from_probe]
  calc
    mapResult toProbe (AspisR1S9SquareMulQMCutV1.field.CM31.add x y) =
        mapResult actualToProbe
          (mapResult AspisR1S9QMSquareMixedProductMapV1.mapActualCM
            (AspisR1S9SquareMulQMCutV1.field.CM31.add x y)) := by
              change mapResult (fun z => actualToProbe (toActual z)) _ = _
              exact (mapResult_comp actualToProbe toActual _).symm
    _ = mapResult actualToProbe
          (AspisR1S9ActualQMMulCutV1.field.CM31.add (toActual x) (toActual y)) :=
        congrArg (mapResult actualToProbe) hstruct
    _ = .ok (AspisR1.R22CanonicalCM31.wrappingCMAdd (toProbe x) (toProbe y)) := hactual
    _ = AspisR1Qm31ArithmeticProbe.field.CM31.add (toProbe x) (toProbe y) :=
        (probe_add_canonical x y hx hy).symm

/-- Combined-cut CM multiplication maps through the actual source-cut implementation
and its retained R22 checked/wrapping contract. -/
theorem combined_cm_mul_maps_to_probe (x y : SCM)
    (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalCM (toProbe x))
    (hy : AspisR1.ExtractedCurrentTowerAdd.CanonicalCM (toProbe y)) :
    mapResult toProbe (AspisR1S9SquareMulQMCutV1.field.CM31.mul x y) =
      AspisR1Qm31ArithmeticProbe.field.CM31.mul (toProbe x) (toProbe y) := by
  have hstruct := AspisR1S9QMSquareMixedProductMapV1.cm_mul_map x y
  have hactual :
      mapResult actualToProbe
        (AspisR1S9ActualQMMulCutV1.field.CM31.mul (toActual x) (toActual y)) =
      .ok (AspisR1.R22CanonicalCM31.wrappingCMMul (toProbe x) (toProbe y)) := by
    rw [AspisR1S9ActualQM31WrappingMapV1.actual_cm_mul_eq_ok]
    simp only [mapResult, AspisR1S9SourceResultTransportV1.mapResult, probe_of_actual_map, actual_from_probe]
  calc
    mapResult toProbe (AspisR1S9SquareMulQMCutV1.field.CM31.mul x y) =
        mapResult actualToProbe
          (mapResult AspisR1S9QMSquareMixedProductMapV1.mapActualCM
            (AspisR1S9SquareMulQMCutV1.field.CM31.mul x y)) := by
              change mapResult (fun z => actualToProbe (toActual z)) _ = _
              exact (mapResult_comp actualToProbe toActual _).symm
    _ = mapResult actualToProbe
          (AspisR1S9ActualQMMulCutV1.field.CM31.mul (toActual x) (toActual y)) :=
        congrArg (mapResult actualToProbe) hstruct
    _ = .ok (AspisR1.R22CanonicalCM31.wrappingCMMul (toProbe x) (toProbe y)) := hactual
    _ = AspisR1Qm31ArithmeticProbe.field.CM31.mul (toProbe x) (toProbe y) :=
        (probe_mul_canonical x y hx hy).symm

/-- Source subtraction has the same checked/wrapping transport. -/
theorem combined_cm_sub_maps_to_probe (x y : SCM)
    (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalCM (toProbe x))
    (hy : AspisR1.ExtractedCurrentTowerAdd.CanonicalCM (toProbe y)) :
    mapResult toProbe (AspisR1S9SquareMulQMCutV1.field.CM31.sub x y) =
      AspisR1Qm31ArithmeticProbe.field.CM31.sub (toProbe x) (toProbe y) := by
  have hstruct := AspisR1S9QMSquareMixedProductMapV1.cm_sub_map x y
  have hactual :
      mapResult actualToProbe
        (AspisR1S9ActualQMMulCutV1.field.CM31.sub (toActual x) (toActual y)) =
      .ok (AspisR1.R22CanonicalCM31.wrappingCMSub (toProbe x) (toProbe y)) := by
    rw [AspisR1S9ActualQM31WrappingMapV1.actual_cm_sub_eq_ok]
    simp only [mapResult, AspisR1S9SourceResultTransportV1.mapResult, probe_of_actual_map, actual_from_probe]
  calc
    mapResult toProbe (AspisR1S9SquareMulQMCutV1.field.CM31.sub x y) =
        mapResult actualToProbe
          (mapResult AspisR1S9QMSquareMixedProductMapV1.mapActualCM
            (AspisR1S9SquareMulQMCutV1.field.CM31.sub x y)) := by
              change mapResult (fun z => actualToProbe (toActual z)) _ = _
              exact (mapResult_comp actualToProbe toActual _).symm
    _ = mapResult actualToProbe
          (AspisR1S9ActualQMMulCutV1.field.CM31.sub (toActual x) (toActual y)) :=
        congrArg (mapResult actualToProbe) hstruct
    _ = .ok (AspisR1.R22CanonicalCM31.wrappingCMSub (toProbe x) (toProbe y)) := hactual
    _ = AspisR1Qm31ArithmeticProbe.field.CM31.sub (toProbe x) (toProbe y) :=
        (probe_sub_canonical x y hx hy).symm

/-- `mul_by_r` from the Combined square cut follows the same mapped source
chain and agrees with checked Probe arithmetic for canonical coordinates. -/
theorem combined_by_r_maps_to_probe (x : SCM)
    (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalCM (toProbe x)) :
    mapResult toProbe (AspisR1S9SquareMulQMCutV1.field.mul_by_r x) =
      AspisR1Qm31ArithmeticProbe.field.mul_by_r (toProbe x) := by
  have hstruct := AspisR1S9QMSquareByRMapV1.by_r_maps_to_actual x
  have hactual :
      mapResult actualToProbe
        (AspisR1S9ActualQMMulCutV1.field.mul_by_r (toActual x)) =
      .ok (AspisR1.R22CanonicalQM31.wrappingByR (toProbe x)) := by
    rw [AspisR1S9ActualQM31WrappingMapV1.actual_mul_by_r_eq_ok]
    simp only [mapResult, AspisR1S9SourceResultTransportV1.mapResult, probe_of_actual_map, actual_from_probe]
  calc
    mapResult toProbe (AspisR1S9SquareMulQMCutV1.field.mul_by_r x) =
        mapResult actualToProbe
          (mapResult AspisR1S9QMSquareByRMapV1.mapCM
            (AspisR1S9SquareMulQMCutV1.field.mul_by_r x)) := by
              change mapResult (fun z => actualToProbe (toActual z)) _ = _
              exact (mapResult_comp actualToProbe toActual _).symm
    _ = mapResult actualToProbe
          (AspisR1S9ActualQMMulCutV1.field.mul_by_r (toActual x)) :=
        congrArg (mapResult actualToProbe) hstruct
    _ = .ok (AspisR1.R22CanonicalQM31.wrappingByR (toProbe x)) := hactual
    _ = AspisR1Qm31ArithmeticProbe.field.mul_by_r (toProbe x) :=
        (AspisR1.R22CanonicalQM31.byR_agrees (toProbe x) hx).symm

#print axioms combined_cm_add_maps_to_probe
#print axioms combined_cm_mul_maps_to_probe
#print axioms combined_cm_sub_maps_to_probe
#print axioms combined_by_r_maps_to_probe

end AspisR1S9QMSquareCombinedProbeOpsV1
