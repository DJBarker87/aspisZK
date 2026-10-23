import S9WideSourceQMAddV1
import S9WideSourceQMSubV1
import S9WideSourceRecordMapV1
import S9ActualQM31WrappingMapV1
import R22CanonicalQM31
import R22CanonicalCM31

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9WideSourceQMCanonicalV1

abbrev QQM := AspisR1S9ActualQMMulCutV1.field.QM31
abbrev ProbeQM := AspisR1Qm31ArithmeticProbe.field.QM31
abbrev ProbeCM := AspisR1Qm31ArithmeticProbe.field.CM31

def toProbeCM := AspisR1S9ActualQM31WrappingMapV1.toProbeCM
def toProbeQM := AspisR1S9ActualQM31WrappingMapV1.toProbeQM
def fromProbeCM (x : ProbeCM) : AspisR1S9ActualQMMulCutV1.field.CM31 := ⟨x.a, x.b⟩

theorem qcut_qm_add_total_canonical (x y : QQM)
    (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM (toProbeQM x))
    (hy : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM (toProbeQM y)) :
    ∃ z, AspisR1S9WideSourceQMAddV1.qcutQMAdd x y = .ok z ∧
      toProbeQM z = AspisR1.R22CanonicalQM31.wrappingQMAdd (toProbeQM x) (toProbeQM y) ∧
      AspisR1.ExtractedCurrentTowerAdd.CanonicalQM (toProbeQM z) ∧
      AspisR1Qm31ArithmeticProbe.field.QM31.add (toProbeQM x) (toProbeQM y) = .ok (toProbeQM z) := by
  let z : QQM := ⟨
    fromProbeCM (AspisR1.R22CanonicalCM31.wrappingCMAdd (toProbeCM x.c0) (toProbeCM y.c0)),
    fromProbeCM (AspisR1.R22CanonicalCM31.wrappingCMAdd (toProbeCM x.c1) (toProbeCM y.c1))⟩
  have hresult : AspisR1S9WideSourceQMAddV1.qcutQMAdd x y = .ok z := by
    simp only [AspisR1S9WideSourceQMAddV1.qcutQMAdd,
      AspisR1S9ActualQM31WrappingMapV1.actual_cm_add_eq_ok, bind_tc_ok,
      z, toProbeQM, toProbeCM, fromProbeCM,
      AspisR1S9ActualQM31WrappingMapV1.toProbeQM,
      AspisR1S9ActualQM31WrappingMapV1.toProbeCM,
      AspisR1S9ActualQM31WrappingMapV1.fromProbeCM]
  have hprobe : toProbeQM z =
      AspisR1.R22CanonicalQM31.wrappingQMAdd (toProbeQM x) (toProbeQM y) := by
    simp only [z, toProbeQM, toProbeCM, fromProbeCM,
      AspisR1S9ActualQM31WrappingMapV1.toProbeQM,
      AspisR1S9ActualQM31WrappingMapV1.toProbeCM,
      AspisR1S9ActualQM31WrappingMapV1.fromProbeCM,
      AspisR1.R22CanonicalQM31.wrappingQMAdd,
      AspisR1.R22CanonicalCM31.wrappingCMAdd]
  refine ⟨z, hresult, hprobe, ?_, ?_⟩
  · rw [hprobe]
    exact AspisR1.R22CanonicalQM31.qm_add_canonical _ _ hx hy
  · rw [hprobe]
    exact AspisR1.R22CanonicalQM31.qm_add_agrees _ _ hx hy

def wrappingQMSub (x y : ProbeQM) : ProbeQM :=
  ⟨AspisR1.R22CanonicalCM31.wrappingCMSub x.c0 y.c0,
    AspisR1.R22CanonicalCM31.wrappingCMSub x.c1 y.c1⟩

theorem qcut_qm_sub_total_canonical (x y : QQM)
    (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM (toProbeQM x))
    (hy : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM (toProbeQM y)) :
    ∃ z, AspisR1S9WideSourceQMSubV1.qcutQMSub x y = .ok z ∧
      toProbeQM z = wrappingQMSub (toProbeQM x) (toProbeQM y) ∧
      AspisR1.ExtractedCurrentTowerAdd.CanonicalQM (toProbeQM z) ∧
      AspisR1Qm31ArithmeticProbe.field.CM31.sub (toProbeCM x.c0) (toProbeCM y.c0) =
        .ok (AspisR1.R22CanonicalCM31.wrappingCMSub (toProbeCM x.c0) (toProbeCM y.c0)) ∧
      AspisR1Qm31ArithmeticProbe.field.CM31.sub (toProbeCM x.c1) (toProbeCM y.c1) =
        .ok (AspisR1.R22CanonicalCM31.wrappingCMSub (toProbeCM x.c1) (toProbeCM y.c1)) := by
  let z : QQM := ⟨
    fromProbeCM (AspisR1.R22CanonicalCM31.wrappingCMSub (toProbeCM x.c0) (toProbeCM y.c0)),
    fromProbeCM (AspisR1.R22CanonicalCM31.wrappingCMSub (toProbeCM x.c1) (toProbeCM y.c1))⟩
  have hresult : AspisR1S9WideSourceQMSubV1.qcutQMSub x y = .ok z := by
    simp only [AspisR1S9WideSourceQMSubV1.qcutQMSub,
      AspisR1S9ActualQM31WrappingMapV1.actual_cm_sub_eq_ok, bind_tc_ok,
      z, toProbeQM, toProbeCM, fromProbeCM,
      AspisR1S9ActualQM31WrappingMapV1.toProbeQM,
      AspisR1S9ActualQM31WrappingMapV1.toProbeCM,
      AspisR1S9ActualQM31WrappingMapV1.fromProbeCM]
  have hprobe : toProbeQM z = wrappingQMSub (toProbeQM x) (toProbeQM y) := by
    simp only [z, toProbeQM, toProbeCM, fromProbeCM, wrappingQMSub,
      AspisR1S9ActualQM31WrappingMapV1.toProbeQM,
      AspisR1S9ActualQM31WrappingMapV1.toProbeCM,
      AspisR1S9ActualQM31WrappingMapV1.fromProbeCM,
      AspisR1.R22CanonicalCM31.wrappingCMSub]
  refine ⟨z, hresult, hprobe, ?_, ?_, ?_⟩
  · rw [hprobe]
    exact ⟨AspisR1.R22CanonicalCM31.cm_sub_canonical _ _ hx.1 hy.1,
      AspisR1.R22CanonicalCM31.cm_sub_canonical _ _ hx.2 hy.2⟩
  · exact AspisR1.R22CanonicalCM31.cm_sub_agrees _ _ hx.1 hy.1
  · exact AspisR1.R22CanonicalCM31.cm_sub_agrees _ _ hx.2 hy.2

theorem qcut_mul_u_total_canonical (x : QQM)
    (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM (toProbeQM x)) :
    ∃ z, AspisR1S9WideSourceRecordMapV1.qcutMulUFormula x = .ok z ∧
      toProbeQM z =
        ⟨AspisR1.R22CanonicalQM31.wrappingByR (toProbeCM x.c1), toProbeCM x.c0⟩ ∧
      AspisR1.ExtractedCurrentTowerAdd.CanonicalQM (toProbeQM z) ∧
      AspisR1Qm31ArithmeticProbe.field.mul_by_r (toProbeCM x.c1) =
        .ok (AspisR1.R22CanonicalQM31.wrappingByR (toProbeCM x.c1)) := by
  let z : QQM := ⟨
    fromProbeCM (AspisR1.R22CanonicalQM31.wrappingByR (toProbeCM x.c1)), x.c0⟩
  have hresult : AspisR1S9WideSourceRecordMapV1.qcutMulUFormula x = .ok z := by
    simp only [AspisR1S9WideSourceRecordMapV1.qcutMulUFormula,
      AspisR1S9ActualQM31WrappingMapV1.actual_mul_by_r_eq_ok, bind_tc_ok,
      z, toProbeQM, toProbeCM, fromProbeCM,
      AspisR1S9ActualQM31WrappingMapV1.toProbeQM,
      AspisR1S9ActualQM31WrappingMapV1.toProbeCM,
      AspisR1S9ActualQM31WrappingMapV1.fromProbeCM]
  have hprobe : toProbeQM z =
      ⟨AspisR1.R22CanonicalQM31.wrappingByR (toProbeCM x.c1), toProbeCM x.c0⟩ := by
    simp only [z, toProbeQM, toProbeCM, fromProbeCM,
      AspisR1S9ActualQM31WrappingMapV1.toProbeQM,
      AspisR1S9ActualQM31WrappingMapV1.toProbeCM,
      AspisR1S9ActualQM31WrappingMapV1.fromProbeCM]
  refine ⟨z, hresult, hprobe, ?_, ?_⟩
  · rw [hprobe]
    exact ⟨AspisR1.R22CanonicalQM31.byR_canonical _ hx.2, hx.1⟩
  · exact AspisR1.R22CanonicalQM31.byR_agrees _ hx.2

#print axioms qcut_qm_add_total_canonical
#print axioms qcut_qm_sub_total_canonical
#print axioms qcut_mul_u_total_canonical

end AspisR1S9WideSourceQMCanonicalV1
