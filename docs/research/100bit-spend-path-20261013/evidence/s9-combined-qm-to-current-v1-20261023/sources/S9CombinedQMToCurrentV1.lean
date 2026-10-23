import S9GeneratedCombinedQMResultV1
import S9QMSquareCanonicalMapV1
import S9ActualQMCurrentHelperMapV1
import KpowersCurrentQMSemanticsV1
import S3S9ConcreteFieldOpsV1
import CurrentWideQMBridge
import S9SourceResultTransportV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9CombinedQMToCurrentV1

abbrev SrcQ := AspisR1S9GeneratedCombinedQMResultV1.SourceQM
abbrev ActQ := AspisR1S9ActualQMCurrentHelperMapV1.ActualQM
abbrev CurQ := AspisR1CurrentWide.field.QM31
abbrev toCurrentQM := AspisR1S9QMSquareCanonicalMapV1.mapQM
abbrev toActualQM := AspisR1S9GeneratedCombinedQMResultV1.mapQM
def mapResult {A B : Type} (f : A → B) (r : Result A) : Result B :=
  AspisR1S9SourceResultTransportV1.mapResult f r

theorem mapResult_comp {A B C : Type} (f : A → B) (g : B → C) (r : Result A) :
    mapResult g (mapResult f r) = mapResult (g ∘ f) r := by
  cases r <;> rfl

theorem actual_to_current_eq (q : SrcQ) :
    AspisR1S9ActualQMCurrentHelperMapV1.actualToCurrent (toActualQM q) =
      toCurrentQM q := by
  cases q with
  | mk c0 c1 => cases c0 <;> cases c1 <;> rfl


private theorem helperToCurrent_bind_roundtrip (r : Result CurQ) :
    mapResult AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM
      (do let z ← r; Result.ok (AspisR1S9HelperP6PowerSemanticsV1.currentToHelperQM z)) = r := by
  cases r <;> simp [mapResult, AspisR1S9SourceResultTransportV1.mapResult,
    AspisR1S9HelperP6PowerSemanticsV1.helperToCurrent_currentToHelper]

theorem actual_qm_mul_to_current
    (x y : ActQ)
    (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM x))
    (hy : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM y)) :
    mapResult AspisR1S9ActualQMCurrentHelperMapV1.actualToCurrent
      (AspisR1S9ActualQMMulCutV1.field.QM31.mul x y) =
      AspisR1CurrentWide.field.QM31.mul
        (AspisR1S9ActualQMCurrentHelperMapV1.actualToCurrent x)
        (AspisR1S9ActualQMCurrentHelperMapV1.actualToCurrent y) := by
  have hm := AspisR1S9ActualQMCurrentHelperMapV1.actual_qm_mul_maps_to_concrete_helper x y hx hy
  have hcompose : ∀ r : Result ActQ,
      mapResult AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM
        (AspisR1S9ActualQMCurrentHelperMapV1.mapResult
          AspisR1S9ActualQMCurrentHelperMapV1.actualToHelper r) =
      mapResult AspisR1S9ActualQMCurrentHelperMapV1.actualToCurrent r := by
    intro r
    cases r <;> rfl
  have hleft := congrArg
    (mapResult AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM) hm
  rw [hcompose] at hleft
  have hright :
      mapResult AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM
        (@AspisR1S9HelperP6.FieldOps.qmMul AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
          (AspisR1S9ActualQMCurrentHelperMapV1.actualToHelper x)
          (AspisR1S9ActualQMCurrentHelperMapV1.actualToHelper y)) =
      AspisR1CurrentWide.field.QM31.mul
        (AspisR1S9ActualQMCurrentHelperMapV1.actualToCurrent x)
        (AspisR1S9ActualQMCurrentHelperMapV1.actualToCurrent y) := by
    rw [AspisR1S9ConcreteFieldOpsV1.concrete_qmMul_is_current]
    rw [AspisR1S9HelperP6PowerSemanticsV1.currentQMSemantics_mul_installs_operation]
    change mapResult AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM
      (do
        let z ← (AspisR1CurrentWide.field.QM31.mul
          (AspisR1S9ActualQMCurrentHelperMapV1.actualToCurrent x)
          (AspisR1S9ActualQMCurrentHelperMapV1.actualToCurrent y))
        Result.ok (AspisR1S9HelperP6PowerSemanticsV1.currentToHelperQM z)) =
      AspisR1CurrentWide.field.QM31.mul
        (AspisR1S9ActualQMCurrentHelperMapV1.actualToCurrent x)
        (AspisR1S9ActualQMCurrentHelperMapV1.actualToCurrent y)
    exact helperToCurrent_bind_roundtrip _
  exact hleft.trans hright

theorem combined_qm_mul_to_current
    (x y : SrcQ)
    (hx : AspisR1CurrentWide.Proof.CanonicalQM (toCurrentQM x))
    (hy : AspisR1CurrentWide.Proof.CanonicalQM (toCurrentQM y)) :
    mapResult toCurrentQM
      (AspisR1S9SquareMulQMCutV1.field.QM31.mul x y) =
      AspisR1CurrentWide.field.QM31.mul (toCurrentQM x) (toCurrentQM y) := by
  have hmap := AspisR1S9GeneratedCombinedQMResultV1.combined_qm_mul_maps x y
  have hprobeX : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM (toActualQM x)) := by
    rw [← AspisR1S9ActualQMCurrentHelperMapV1.probe_actualToCurrent (toActualQM x),
      actual_to_current_eq]
    exact hx
  have hprobeY : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM (toActualQM y)) := by
    rw [← AspisR1S9ActualQMCurrentHelperMapV1.probe_actualToCurrent (toActualQM y),
      actual_to_current_eq]
    exact hy
  have hactual := actual_qm_mul_to_current (toActualQM x) (toActualQM y) hprobeX hprobeY
  have hcompose : toCurrentQM =
      (AspisR1S9ActualQMCurrentHelperMapV1.actualToCurrent ∘ toActualQM) := by
    funext z
    exact (actual_to_current_eq z).symm
  calc
    mapResult toCurrentQM (AspisR1S9SquareMulQMCutV1.field.QM31.mul x y) =
      mapResult (AspisR1S9ActualQMCurrentHelperMapV1.actualToCurrent ∘ toActualQM)
        (AspisR1S9SquareMulQMCutV1.field.QM31.mul x y) :=
          congrArg (fun f => mapResult f
            (AspisR1S9SquareMulQMCutV1.field.QM31.mul x y)) hcompose
    _ = mapResult AspisR1S9ActualQMCurrentHelperMapV1.actualToCurrent
        (mapResult toActualQM (AspisR1S9SquareMulQMCutV1.field.QM31.mul x y)) :=
          (mapResult_comp toActualQM
            AspisR1S9ActualQMCurrentHelperMapV1.actualToCurrent _).symm
    _ = mapResult AspisR1S9ActualQMCurrentHelperMapV1.actualToCurrent
        (AspisR1S9ActualQMMulCutV1.field.QM31.mul (toActualQM x) (toActualQM y)) :=
          congrArg (mapResult AspisR1S9ActualQMCurrentHelperMapV1.actualToCurrent) hmap
    _ = AspisR1CurrentWide.field.QM31.mul
        (AspisR1S9ActualQMCurrentHelperMapV1.actualToCurrent (toActualQM x))
        (AspisR1S9ActualQMCurrentHelperMapV1.actualToCurrent (toActualQM y)) := hactual
    _ = AspisR1CurrentWide.field.QM31.mul (toCurrentQM x) (toCurrentQM y) := by
          rw [actual_to_current_eq, actual_to_current_eq]

#print axioms actual_qm_mul_to_current
#print axioms combined_qm_mul_to_current

end AspisR1S9CombinedQMToCurrentV1
