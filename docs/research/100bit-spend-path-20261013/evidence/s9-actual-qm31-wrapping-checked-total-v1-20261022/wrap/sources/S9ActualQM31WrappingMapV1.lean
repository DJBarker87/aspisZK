import AspisR1S9ActualQMMulCutV1.Funs
import S9QMMulM31PrimitiveSourceBridgeV1
import S9ActualCM31WrappingMapV1
import R22CanonicalCM31
import R22CanonicalQM31

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9ActualQM31WrappingMapV1

abbrev ActualCM := AspisR1S9ActualQMMulCutV1.field.CM31
abbrev ProbeCM := AspisR1Qm31ArithmeticProbe.field.CM31
abbrev ActualQM := AspisR1S9ActualQMMulCutV1.field.QM31
abbrev ProbeQM := AspisR1Qm31ArithmeticProbe.field.QM31

def toProbeCM (x : ActualCM) : ProbeCM := ⟨x.a, x.b⟩
def fromProbeCM (x : ProbeCM) : ActualCM := ⟨x.a, x.b⟩
def toProbeQM (x : ActualQM) : ProbeQM :=
  ⟨toProbeCM x.c0, toProbeCM x.c1⟩

private theorem from_to_probe_cm (x : ActualCM) : fromProbeCM (toProbeCM x) = x := by
  cases x
  rfl

private theorem to_from_probe_cm (x : ProbeCM) : toProbeCM (fromProbeCM x) = x := by
  cases x
  rfl

theorem actual_cm_add_wrapping
    (x y : AspisR1S9ActualQMMulCutV1.field.CM31) :
    (do
      let z ← AspisR1S9ActualQMMulCutV1.field.CM31.add x y
      .ok (toProbeCM z)) =
      .ok (AspisR1.R22CanonicalCM31.wrappingCMAdd (toProbeCM x) (toProbeCM y)) := by
  simp only [AspisR1S9ActualQMMulCutV1.field.CM31.add,
    AspisR1S9QMMulM31PrimitiveSourceBridgeV1.actual_m31_add_eq_r22_wrapping,
    bind_tc_ok, toProbeCM, AspisR1.R22CanonicalCM31.wrappingCMAdd]

theorem actual_cm_sub_wrapping
    (x y : AspisR1S9ActualQMMulCutV1.field.CM31) :
    (do
      let z ← AspisR1S9ActualQMMulCutV1.field.CM31.sub x y
      .ok (toProbeCM z)) =
      .ok (AspisR1.R22CanonicalCM31.wrappingCMSub (toProbeCM x) (toProbeCM y)) := by
  simp only [AspisR1S9ActualQMMulCutV1.field.CM31.sub,
    AspisR1S9QMMulM31PrimitiveSourceBridgeV1.actual_m31_sub_eq_r22_wrapping,
    bind_tc_ok, toProbeCM, AspisR1.R22CanonicalCM31.wrappingCMSub]

theorem actual_mul_by_r_wrapping
    (x : AspisR1S9ActualQMMulCutV1.field.CM31) :
    (do
      let z ← AspisR1S9ActualQMMulCutV1.field.mul_by_r x
      .ok (toProbeCM z)) =
      .ok (AspisR1.R22CanonicalQM31.wrappingByR (toProbeCM x)) := by
  simp only [AspisR1S9ActualQMMulCutV1.field.mul_by_r,
    AspisR1S9ActualQMMulCutV1.field.M31.double,
    AspisR1S9QMMulM31PrimitiveSourceBridgeV1.actual_m31_add_eq_r22_wrapping,
    AspisR1S9QMMulM31PrimitiveSourceBridgeV1.actual_m31_sub_eq_r22_wrapping,
    bind_tc_ok, toProbeCM, AspisR1.R22CanonicalQM31.wrappingByR,
    AspisR1.R22CanonicalM31AddSub.wrappingAdd,
    AspisR1.R22CanonicalM31AddSub.wrappingSub]


private theorem source_result_of_mapped_ok {α β : Type}
    (f : α → β) (g : β → α) (hgf : ∀ x, g (f x) = x)
    (r : Result α) (z : β)
    (h : (do let x ← r; .ok (f x)) = .ok z) :
    r = .ok (g z) := by
  cases r with
  | ok v =>
      simp only [bind_tc_ok] at h
      apply congrArg Result.ok
      calc
        v = g (f v) := (hgf v).symm
        _ = g z := congrArg g (Result.ok.inj h)
  | fail e =>
      simp only [bind_tc_fail] at h
      cases h
  | div =>
      simp only [bind_tc_div] at h
      cases h

theorem actual_cm_mul_eq_ok
    (x y : ActualCM) :
    AspisR1S9ActualQMMulCutV1.field.CM31.mul x y =
      .ok (fromProbeCM (AspisR1.R22CanonicalCM31.wrappingCMMul
        (toProbeCM x) (toProbeCM y))) :=
  source_result_of_mapped_ok toProbeCM fromProbeCM from_to_probe_cm _ _
    (AspisR1S9ActualCM31WrappingMapV1.actual_cm_mul_wrapping x y)

theorem actual_cm_add_eq_ok
    (x y : ActualCM) :
    AspisR1S9ActualQMMulCutV1.field.CM31.add x y =
      .ok (fromProbeCM (AspisR1.R22CanonicalCM31.wrappingCMAdd
        (toProbeCM x) (toProbeCM y))) :=
  source_result_of_mapped_ok toProbeCM fromProbeCM from_to_probe_cm _ _
    (actual_cm_add_wrapping x y)

theorem actual_cm_sub_eq_ok
    (x y : ActualCM) :
    AspisR1S9ActualQMMulCutV1.field.CM31.sub x y =
      .ok (fromProbeCM (AspisR1.R22CanonicalCM31.wrappingCMSub
        (toProbeCM x) (toProbeCM y))) :=
  source_result_of_mapped_ok toProbeCM fromProbeCM from_to_probe_cm _ _
    (actual_cm_sub_wrapping x y)

theorem actual_mul_by_r_eq_ok
    (x : ActualCM) :
    AspisR1S9ActualQMMulCutV1.field.mul_by_r x =
      .ok (fromProbeCM (AspisR1.R22CanonicalQM31.wrappingByR (toProbeCM x))) :=
  source_result_of_mapped_ok toProbeCM fromProbeCM from_to_probe_cm _ _
    (actual_mul_by_r_wrapping x)

theorem actual_qm_mul_graph (x y : ActualQM) :
    AspisR1S9ActualQMMulCutV1.field.QM31.mul x y = (do
      let m0 ← AspisR1S9ActualQMMulCutV1.field.CM31.mul x.c0 y.c0
      let m1 ← AspisR1S9ActualQMMulCutV1.field.CM31.mul x.c1 y.c1
      let c ← AspisR1S9ActualQMMulCutV1.field.CM31.add x.c0 x.c1
      let c1 ← AspisR1S9ActualQMMulCutV1.field.CM31.add y.c0 y.c1
      let m2 ← AspisR1S9ActualQMMulCutV1.field.CM31.mul c c1
      let c2 ← AspisR1S9ActualQMMulCutV1.field.mul_by_r m1
      let c3 ← AspisR1S9ActualQMMulCutV1.field.CM31.add m0 c2
      let c4 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub m2 m0
      let c5 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub c4 m1
      .ok ⟨c3, c5⟩) := by
  simp only [AspisR1S9ActualQMMulCutV1.field.QM31.mul, bind_assoc_eq]

theorem actual_qm_mul_wrapping
    (x y : ActualQM) :
    (do
      let z ← AspisR1S9ActualQMMulCutV1.field.QM31.mul x y
      .ok (toProbeQM z)) =
      .ok (AspisR1.R22CanonicalQM31.wrappingQMMul (toProbeQM x) (toProbeQM y)) := by
  rw [actual_qm_mul_graph]
  simp only [actual_cm_mul_eq_ok,
    actual_cm_add_eq_ok, actual_mul_by_r_eq_ok, actual_cm_sub_eq_ok,
    bind_tc_ok, toProbeCM, toProbeQM, to_from_probe_cm,
    AspisR1.R22CanonicalQM31.wrappingQMMul]
  rfl

#print axioms actual_cm_mul_eq_ok
#print axioms actual_cm_add_eq_ok
#print axioms actual_cm_sub_eq_ok
#print axioms actual_mul_by_r_eq_ok
#print axioms actual_qm_mul_graph
#print axioms actual_qm_mul_wrapping

end AspisR1S9ActualQM31WrappingMapV1
