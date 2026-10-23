import S9WideSourceQMCanonicalV1
import S9ActualQMCurrentHelperMapV1
import CurrentWideQMBridge
import S9CurrentWideQMSubBridgeV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9WideSourceQMCurrentOpsV1

abbrev Q := AspisR1S9ActualQMMulCutV1.field.QM31
abbrev C := AspisR1CurrentWide.field.QM31
abbrev ProbeQ := AspisR1Qm31ArithmeticProbe.field.QM31

def qToCurrent (x : Q) : C :=
  AspisR1S9ActualQMCurrentHelperMapV1.actualToCurrent x

abbrev mapResult {A B : Type} (f : A → B) (r : Result A) : Result B :=
  AspisR1S9ActualQMCurrentHelperMapV1.mapResult f r

private theorem mapResult_injective {A B : Type} (f : A → B)
    (hf : ∀ x y, f x = f y → x = y) (r s : Result A)
    (h : mapResult f r = mapResult f s) : r = s := by
  cases r with
  | fail e => cases s with
    | fail e' =>
      change Result.fail e = Result.fail e' at h
      cases h
      rfl
    | div => change Result.fail e = Result.div at h; cases h
    | ok y => change Result.fail e = Result.ok (f y) at h; cases h
  | div => cases s with
    | fail e => change Result.div = Result.fail e at h; cases h
    | div => rfl
    | ok y => change Result.div = Result.ok (f y) at h; cases h
  | ok x => cases s with
    | fail e => change Result.ok (f x) = Result.fail e at h; cases h
    | div => change Result.ok (f x) = Result.div at h; cases h
    | ok y =>
      change Result.ok (f x) = Result.ok (f y) at h
      have hxy := Result.ok.inj h
      have hxy' := hf x y hxy
      cases hxy'
      rfl

private theorem mapResult_comp {A B D : Type} (f : A → B) (g : B → D)
    (r : Result A) :
    mapResult g (mapResult f r) = mapResult (fun x => g (f x)) r := by
  cases r <;> rfl

private theorem probe_qToCurrent (x : Q) :
    AspisR1CurrentWide.Proof.toQM (qToCurrent x) =
      AspisR1S9ActualQM31WrappingMapV1.toProbeQM x :=
  AspisR1S9ActualQMCurrentHelperMapV1.probe_actualToCurrent x

private theorem current_qToProbe_c0 (x : Q) :
    AspisR1CurrentWide.Proof.toCM (qToCurrent x).c0 =
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM x).c0 := by
  have h := congrArg (fun p : ProbeQ => p.c0) (probe_qToCurrent x)
  simpa [AspisR1CurrentWide.Proof.toQM] using h

private theorem current_qToProbe_c1 (x : Q) :
    AspisR1CurrentWide.Proof.toCM (qToCurrent x).c1 =
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM x).c1 := by
  have h := congrArg (fun p : ProbeQ => p.c1) (probe_qToCurrent x)
  simpa [AspisR1CurrentWide.Proof.toQM] using h

private theorem currentProbe_comp (r : Result Q) :
    mapResult AspisR1CurrentWide.Proof.toQM (mapResult qToCurrent r) =
      mapResult AspisR1S9ActualQM31WrappingMapV1.toProbeQM r := by
  cases r with
  | fail e => rfl
  | div => rfl
  | ok x =>
    change Result.ok (AspisR1CurrentWide.Proof.toQM (qToCurrent x)) =
      Result.ok (AspisR1S9ActualQM31WrappingMapV1.toProbeQM x)
    exact congrArg Result.ok (probe_qToCurrent x)

private theorem current_qm_add_to_probe (x y : C) :
    mapResult AspisR1CurrentWide.Proof.toQM
      (AspisR1CurrentWide.field.QM31.add x y) =
      AspisR1Qm31ArithmeticProbe.field.QM31.add
        (AspisR1CurrentWide.Proof.toQM x) (AspisR1CurrentWide.Proof.toQM y) := by
  exact (AspisR1S9ActualQMCurrentHelperMapV1.mapResult_eq_bind _ _).trans
    (AspisR1CurrentWide.Proof.qm_add_same x y)

private theorem current_qm_mul_to_probe (x y : C) :
    mapResult AspisR1CurrentWide.Proof.toQM
      (AspisR1CurrentWide.field.QM31.mul x y) =
      AspisR1Qm31ArithmeticProbe.field.QM31.mul
        (AspisR1CurrentWide.Proof.toQM x) (AspisR1CurrentWide.Proof.toQM y) := by
  exact (AspisR1S9ActualQMCurrentHelperMapV1.mapResult_eq_bind _ _).trans
    (AspisR1CurrentWide.Proof.qm_mul_same x y)

private theorem current_qm_sub_to_probe (x y : C) :
    mapResult AspisR1CurrentWide.Proof.toQM
      (AspisR1CurrentWide.field.QM31.sub x y) =
      (do
        let c ← AspisR1Qm31ArithmeticProbe.field.CM31.sub
          (AspisR1CurrentWide.Proof.toCM x.c0) (AspisR1CurrentWide.Proof.toCM y.c0)
        let c1 ← AspisR1Qm31ArithmeticProbe.field.CM31.sub
          (AspisR1CurrentWide.Proof.toCM x.c1) (AspisR1CurrentWide.Proof.toCM y.c1)
        ok { c0 := c, c1 := c1 }) := by
  exact (AspisR1S9ActualQMCurrentHelperMapV1.mapResult_eq_bind _ _).trans
    (AspisR1CurrentWide.Proof.qm_sub_same_wide x y)

/-- The qcut addition and the checked CurrentWide addition have identical
full Result behavior after the explicit carrier map, on canonical inputs.
The premise is needed because the source cut is wrapping while CurrentWide
uses checked operations. -/
theorem qcut_qm_add_maps_to_current (x y : Q)
    (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM x))
    (hy : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM y)) :
    mapResult qToCurrent
      (AspisR1S9WideSourceQMAddV1.qcutQMAdd x y) =
      AspisR1CurrentWide.field.QM31.add (qToCurrent x) (qToCurrent y) := by
  obtain ⟨z, hq, hzprobe, hzcan, hprobe⟩ :=
    AspisR1S9WideSourceQMCanonicalV1.qcut_qm_add_total_canonical x y hx hy
  have hsourceProbe :
      mapResult AspisR1S9ActualQM31WrappingMapV1.toProbeQM
        (AspisR1S9WideSourceQMAddV1.qcutQMAdd x y) =
      AspisR1Qm31ArithmeticProbe.field.QM31.add
        (AspisR1S9ActualQM31WrappingMapV1.toProbeQM x)
        (AspisR1S9ActualQM31WrappingMapV1.toProbeQM y) := by
    rw [hq]
    exact hprobe.symm
  have htargetProbe :
      mapResult AspisR1CurrentWide.Proof.toQM
        (AspisR1CurrentWide.field.QM31.add (qToCurrent x) (qToCurrent y)) =
      AspisR1Qm31ArithmeticProbe.field.QM31.add
        (AspisR1S9ActualQM31WrappingMapV1.toProbeQM x)
        (AspisR1S9ActualQM31WrappingMapV1.toProbeQM y) := by
    rw [current_qm_add_to_probe, probe_qToCurrent, probe_qToCurrent]
  have hmaps :
      mapResult AspisR1CurrentWide.Proof.toQM
        (mapResult qToCurrent
          (AspisR1S9WideSourceQMAddV1.qcutQMAdd x y)) =
      mapResult AspisR1CurrentWide.Proof.toQM
        (AspisR1CurrentWide.field.QM31.add (qToCurrent x) (qToCurrent y)) := by
    calc
      _ = mapResult AspisR1S9ActualQM31WrappingMapV1.toProbeQM
            (AspisR1S9WideSourceQMAddV1.qcutQMAdd x y) := by
          exact currentProbe_comp _
      _ = _ := hsourceProbe.trans htargetProbe.symm
  exact mapResult_injective AspisR1CurrentWide.Proof.toQM
    AspisR1S9ActualQMCurrentHelperMapV1.currentProbe_injective _ _ hmaps

/-- Same-result bridge for qcut subtraction. The cut theorem retains both
component checked-subtraction equations; CurrentWide's source equation is
compared in Probe carrier without erasing failure behavior. -/
theorem qcut_qm_sub_maps_to_current (x y : Q)
    (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM x))
    (hy : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM y)) :
    mapResult qToCurrent
      (AspisR1S9WideSourceQMSubV1.qcutQMSub x y) =
      AspisR1CurrentWide.field.QM31.sub (qToCurrent x) (qToCurrent y) := by
  obtain ⟨z, hq, hzprobe, hzcan, hsub0, hsub1⟩ :=
    AspisR1S9WideSourceQMCanonicalV1.qcut_qm_sub_total_canonical x y hx hy
  have hsourceProbe :
      mapResult AspisR1S9ActualQM31WrappingMapV1.toProbeQM
        (AspisR1S9WideSourceQMSubV1.qcutQMSub x y) =
      (do
        let c ← AspisR1Qm31ArithmeticProbe.field.CM31.sub
          (AspisR1S9ActualQM31WrappingMapV1.toProbeQM x).c0
          (AspisR1S9ActualQM31WrappingMapV1.toProbeQM y).c0
        let c1 ← AspisR1Qm31ArithmeticProbe.field.CM31.sub
          (AspisR1S9ActualQM31WrappingMapV1.toProbeQM x).c1
          (AspisR1S9ActualQM31WrappingMapV1.toProbeQM y).c1
        ok ({ c0 := c, c1 := c1 } : ProbeQ)) := by
    have hzprobe' : AspisR1S9ActualQM31WrappingMapV1.toProbeQM z =
        AspisR1S9WideSourceQMCanonicalV1.wrappingQMSub
          (AspisR1S9ActualQM31WrappingMapV1.toProbeQM x)
          (AspisR1S9ActualQM31WrappingMapV1.toProbeQM y) := by
      simpa [AspisR1S9WideSourceQMCanonicalV1.toProbeQM,
        AspisR1S9WideSourceQMCanonicalV1.toProbeCM,
        AspisR1S9ActualQM31WrappingMapV1.toProbeQM,
        AspisR1S9ActualQM31WrappingMapV1.toProbeCM] using hzprobe
    have hsub0' : AspisR1Qm31ArithmeticProbe.field.CM31.sub
        (AspisR1S9ActualQM31WrappingMapV1.toProbeCM x.c0)
        (AspisR1S9ActualQM31WrappingMapV1.toProbeCM y.c0) =
        .ok (AspisR1.R22CanonicalCM31.wrappingCMSub
          (AspisR1S9ActualQM31WrappingMapV1.toProbeCM x.c0)
          (AspisR1S9ActualQM31WrappingMapV1.toProbeCM y.c0)) := by
      simpa [AspisR1S9WideSourceQMCanonicalV1.toProbeCM,
        AspisR1S9ActualQM31WrappingMapV1.toProbeCM] using hsub0
    have hsub1' : AspisR1Qm31ArithmeticProbe.field.CM31.sub
        (AspisR1S9ActualQM31WrappingMapV1.toProbeCM x.c1)
        (AspisR1S9ActualQM31WrappingMapV1.toProbeCM y.c1) =
        .ok (AspisR1.R22CanonicalCM31.wrappingCMSub
          (AspisR1S9ActualQM31WrappingMapV1.toProbeCM x.c1)
          (AspisR1S9ActualQM31WrappingMapV1.toProbeCM y.c1)) := by
      simpa [AspisR1S9WideSourceQMCanonicalV1.toProbeCM,
        AspisR1S9ActualQM31WrappingMapV1.toProbeCM] using hsub1
    rw [hq]
    simp only [AspisR1S9ActualQMCurrentHelperMapV1.mapResult, hzprobe',
      AspisR1S9ActualQM31WrappingMapV1.toProbeQM]
    simp only [AspisR1S9WideSourceQMCanonicalV1.wrappingQMSub,
      hsub0', hsub1', bind_tc_ok]
    simpa only [AspisR1S9ActualQM31WrappingMapV1.toProbeQM,
      AspisR1S9WideSourceQMCanonicalV1.wrappingQMSub] using
      congrArg (fun v : ProbeQ => Result.ok v) hzprobe'
  have htargetProbe :
      mapResult AspisR1CurrentWide.Proof.toQM
        (AspisR1CurrentWide.field.QM31.sub (qToCurrent x) (qToCurrent y)) =
      (do
        let c ← AspisR1Qm31ArithmeticProbe.field.CM31.sub
          (AspisR1CurrentWide.Proof.toCM (qToCurrent x).c0)
          (AspisR1CurrentWide.Proof.toCM (qToCurrent y).c0)
        let c1 ← AspisR1Qm31ArithmeticProbe.field.CM31.sub
          (AspisR1CurrentWide.Proof.toCM (qToCurrent x).c1)
          (AspisR1CurrentWide.Proof.toCM (qToCurrent y).c1)
        ok ({ c0 := c, c1 := c1 } : ProbeQ)) := by
    exact current_qm_sub_to_probe _ _
  have hsub_probe :
      (do
        let c ← AspisR1Qm31ArithmeticProbe.field.CM31.sub
          (AspisR1S9ActualQM31WrappingMapV1.toProbeQM x).c0
          (AspisR1S9ActualQM31WrappingMapV1.toProbeQM y).c0
        let c1 ← AspisR1Qm31ArithmeticProbe.field.CM31.sub
          (AspisR1S9ActualQM31WrappingMapV1.toProbeQM x).c1
          (AspisR1S9ActualQM31WrappingMapV1.toProbeQM y).c1
        ok ({ c0 := c, c1 := c1 } : ProbeQ)) =
      (do
        let c ← AspisR1Qm31ArithmeticProbe.field.CM31.sub
          (AspisR1CurrentWide.Proof.toCM (qToCurrent x).c0)
          (AspisR1CurrentWide.Proof.toCM (qToCurrent y).c0)
        let c1 ← AspisR1Qm31ArithmeticProbe.field.CM31.sub
          (AspisR1CurrentWide.Proof.toCM (qToCurrent x).c1)
          (AspisR1CurrentWide.Proof.toCM (qToCurrent y).c1)
        ok ({ c0 := c, c1 := c1 } : ProbeQ)) := by
    rw [← current_qToProbe_c0 x, ← current_qToProbe_c0 y,
      ← current_qToProbe_c1 x, ← current_qToProbe_c1 y]
  have hmaps :
      mapResult AspisR1CurrentWide.Proof.toQM
        (mapResult qToCurrent
          (AspisR1S9WideSourceQMSubV1.qcutQMSub x y)) =
      mapResult AspisR1CurrentWide.Proof.toQM
        (AspisR1CurrentWide.field.QM31.sub (qToCurrent x) (qToCurrent y)) := by
    calc
      _ = mapResult AspisR1S9ActualQM31WrappingMapV1.toProbeQM
            (AspisR1S9WideSourceQMSubV1.qcutQMSub x y) := by
          exact currentProbe_comp _
      _ = _ := hsourceProbe.trans (hsub_probe.trans htargetProbe.symm)
  exact mapResult_injective AspisR1CurrentWide.Proof.toQM
    AspisR1S9ActualQMCurrentHelperMapV1.currentProbe_injective _ _ hmaps

#print axioms qcut_qm_add_maps_to_current
#print axioms qcut_qm_sub_maps_to_current

end AspisR1S9WideSourceQMCurrentOpsV1
