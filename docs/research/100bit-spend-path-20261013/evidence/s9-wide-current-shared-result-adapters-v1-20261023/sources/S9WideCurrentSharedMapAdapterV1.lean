import S9WideSourceQMCurrentOpsV1
import S9WideSourceQMMulCurrentV1
import S9WideSourceMulUCurrentV1
import S9WideSourceRecordMapV1
import S9SourceResultTransportV1
import CurrentWideQMBridge

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9WideCurrentSharedMapAdapterV1

/-- The two existing Result mappers have the same behavior. This explicit
function-head equality lets downstream bind transport use the shared mapper
without unfolding a generated source operation call. -/
theorem actual_mapResult_eq_shared {A B : Type} (f : A → B) :
    (fun r : Result A => AspisR1S9ActualQMCurrentHelperMapV1.mapResult f r) =
      AspisR1S9SourceResultTransportV1.mapResult f := by
  funext r
  cases r <;> rfl

abbrev Q := AspisR1S9ActualQMMulCutV1.field.QM31
abbrev C := AspisR1CurrentWide.field.QM31

def qToCurrent := AspisR1S9WideSourceQMCurrentOpsV1.qToCurrent

/-- Shared-mapper spelling of the existing actual add bridge. -/
theorem qcut_qm_add_maps_to_current (x y : Q)
    (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM x))
    (hy : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM y)) :
    AspisR1S9SourceResultTransportV1.mapResult qToCurrent
      (AspisR1S9WideSourceQMAddV1.qcutQMAdd x y) =
      AspisR1CurrentWide.field.QM31.add (qToCurrent x) (qToCurrent y) := by
  have h := AspisR1S9WideSourceQMCurrentOpsV1.qcut_qm_add_maps_to_current x y hx hy
  have hh := actual_mapResult_eq_shared qToCurrent
  calc
    AspisR1S9SourceResultTransportV1.mapResult qToCurrent
        (AspisR1S9WideSourceQMAddV1.qcutQMAdd x y) =
      AspisR1S9ActualQMCurrentHelperMapV1.mapResult qToCurrent
        (AspisR1S9WideSourceQMAddV1.qcutQMAdd x y) := by
          exact congrArg (fun m : Result Q → Result C => m
            (AspisR1S9WideSourceQMAddV1.qcutQMAdd x y)) hh.symm
    _ = _ := h

/-- Shared-mapper spelling of the existing actual sub bridge. -/
theorem qcut_qm_sub_maps_to_current (x y : Q)
    (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM x))
    (hy : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM y)) :
    AspisR1S9SourceResultTransportV1.mapResult qToCurrent
      (AspisR1S9WideSourceQMSubV1.qcutQMSub x y) =
      AspisR1CurrentWide.field.QM31.sub (qToCurrent x) (qToCurrent y) := by
  have h := AspisR1S9WideSourceQMCurrentOpsV1.qcut_qm_sub_maps_to_current x y hx hy
  have hh := actual_mapResult_eq_shared qToCurrent
  calc
    AspisR1S9SourceResultTransportV1.mapResult qToCurrent
        (AspisR1S9WideSourceQMSubV1.qcutQMSub x y) =
      AspisR1S9ActualQMCurrentHelperMapV1.mapResult qToCurrent
        (AspisR1S9WideSourceQMSubV1.qcutQMSub x y) := by
          exact congrArg (fun m : Result Q → Result C => m
            (AspisR1S9WideSourceQMSubV1.qcutQMSub x y)) hh.symm
    _ = _ := h

/-- Shared-mapper spelling of the existing actual QM multiplication bridge. -/
theorem qcut_qm_mul_maps_to_current (x y : Q)
    (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM x))
    (hy : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM y)) :
    AspisR1S9SourceResultTransportV1.mapResult qToCurrent
      (AspisR1S9ActualQMMulCutV1.field.QM31.mul x y) =
      AspisR1CurrentWide.field.QM31.mul (qToCurrent x) (qToCurrent y) := by
  have h := AspisR1S9WideSourceQMMulCurrentV1.qcut_qm_mul_maps_to_current x y hx hy
  have hh := actual_mapResult_eq_shared qToCurrent
  calc
    AspisR1S9SourceResultTransportV1.mapResult qToCurrent
        (AspisR1S9ActualQMMulCutV1.field.QM31.mul x y) =
      AspisR1S9ActualQMCurrentHelperMapV1.mapResult qToCurrent
        (AspisR1S9ActualQMMulCutV1.field.QM31.mul x y) := by
          exact congrArg (fun m : Result Q → Result C => m
            (AspisR1S9ActualQMMulCutV1.field.QM31.mul x y)) hh.symm
    _ = _ := h

/-- Shared-mapper spelling of the same-run canonical mul-u bridge. -/
theorem qcut_mul_u_maps_to_current (x : Q)
    (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM x)) :
    AspisR1S9SourceResultTransportV1.mapResult qToCurrent
      (AspisR1S9WideSourceRecordMapV1.qcutMulUFormula x) =
      AspisR1CurrentWide.field.wide_exact.mul_u (qToCurrent x) := by
  have h := AspisR1S9WideSourceMulUCurrentV1.qcut_mul_u_maps_to_current x hx
  have hh := actual_mapResult_eq_shared qToCurrent
  calc
    AspisR1S9SourceResultTransportV1.mapResult qToCurrent
        (AspisR1S9WideSourceRecordMapV1.qcutMulUFormula x) =
      AspisR1S9ActualQMCurrentHelperMapV1.mapResult qToCurrent
        (AspisR1S9WideSourceRecordMapV1.qcutMulUFormula x) := by
          exact congrArg (fun m : Result Q → Result C => m
            (AspisR1S9WideSourceRecordMapV1.qcutMulUFormula x)) hh.symm
    _ = _ := h

#print axioms actual_mapResult_eq_shared
#print axioms qcut_qm_add_maps_to_current
#print axioms qcut_qm_mul_maps_to_current
#print axioms qcut_qm_sub_maps_to_current
#print axioms qcut_mul_u_maps_to_current

end AspisR1S9WideCurrentSharedMapAdapterV1
