import S9WideSourceQMCurrentOpsV1
import S9WideSourceRecordMapV1
import CurrentWideBaseBridge
import R22CanonicalQM31

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9WideSourceMulUCurrentV1

abbrev CutCM := AspisR1S9ActualQMMulCutV1.field.CM31
abbrev CutQM := AspisR1S9ActualQMMulCutV1.field.QM31
abbrev CurrentCM := AspisR1CurrentWide.field.CM31
abbrev CurrentQM := AspisR1CurrentWide.field.QM31
abbrev ProbeCM := AspisR1Qm31ArithmeticProbe.field.CM31
abbrev ProbeQM := AspisR1Qm31ArithmeticProbe.field.QM31

def cmToCurrent (x : CutCM) : CurrentCM := ⟨x.a, x.b⟩
def qmToCurrent := AspisR1S9WideSourceQMCurrentOpsV1.qToCurrent

abbrev mapResult {A B : Type} (f : A → B) (r : Result A) : Result B :=
  AspisR1S9ActualQMCurrentHelperMapV1.mapResult f r

private theorem probe_cmToCurrent (x : CutCM) :
    AspisR1CurrentWide.Proof.toCM (cmToCurrent x) =
      AspisR1S9ActualQM31WrappingMapV1.toProbeCM x := by
  cases x
  rfl

private theorem currentProbe_cm_injective (x y : CurrentCM)
    (h : AspisR1CurrentWide.Proof.toCM x = AspisR1CurrentWide.Proof.toCM y) :
    x = y := by
  cases x
  cases y
  simp only [AspisR1CurrentWide.Proof.toCM] at h
  cases h
  rfl

private theorem result_map_injective {A B : Type} (f : A → B)
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

private theorem mapResult_bind_eq {A B C D : Type}
    (g : A → B) (f : C → D) (source : Result A) (target : Result B)
    (sourceNext : A → Result C) (targetNext : B → Result D)
    (hfirst : mapResult g source = target)
    (hnext : ∀ x, mapResult f (sourceNext x) = targetNext (g x)) :
    mapResult f (source >>= sourceNext) = target >>= targetNext := by
  rw [← hfirst]
  cases source with
  | fail e => rfl
  | div => rfl
  | ok x => exact hnext x

private theorem probe_qmToCurrent (x : CutQM) :
    AspisR1CurrentWide.Proof.toQM (qmToCurrent x) =
      AspisR1S9ActualQM31WrappingMapV1.toProbeQM x :=
  AspisR1S9ActualQMCurrentHelperMapV1.probe_actualToCurrent x

private theorem currentProbe_comp (r : Result CutCM) :
    mapResult AspisR1CurrentWide.Proof.toCM (mapResult cmToCurrent r) =
      mapResult AspisR1S9ActualQM31WrappingMapV1.toProbeCM r := by
  cases r with
  | fail e => rfl
  | div => rfl
  | ok x =>
    change Result.ok (AspisR1CurrentWide.Proof.toCM (cmToCurrent x)) =
      Result.ok (AspisR1S9ActualQM31WrappingMapV1.toProbeCM x)
    exact congrArg Result.ok (probe_cmToCurrent x)

private theorem current_mul_by_r_to_probe (x : CurrentCM) :
    mapResult AspisR1CurrentWide.Proof.toCM
      (AspisR1CurrentWide.field.mul_by_r x) =
      AspisR1Qm31ArithmeticProbe.field.mul_by_r
        (AspisR1CurrentWide.Proof.toCM x) := by
  exact (AspisR1S9ActualQMCurrentHelperMapV1.mapResult_eq_bind _ _).trans
    (AspisR1CurrentWide.Proof.mul_by_r_same x)

/-- Same full-Result map for the actual cut `mul_by_r` to CurrentWide's
checked operation. Canonicality is explicit at the wrapping→checked seam. -/
theorem qcut_mul_by_r_maps_to_current (x : CutCM)
    (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalCM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeCM x)) :
    mapResult cmToCurrent (AspisR1S9ActualQMMulCutV1.field.mul_by_r x) =
      AspisR1CurrentWide.field.mul_by_r (cmToCurrent x) := by
  have hsourceProbe :
      mapResult AspisR1S9ActualQM31WrappingMapV1.toProbeCM
        (AspisR1S9ActualQMMulCutV1.field.mul_by_r x) =
      .ok (AspisR1.R22CanonicalQM31.wrappingByR
        (AspisR1S9ActualQM31WrappingMapV1.toProbeCM x)) := by
    rw [AspisR1S9ActualQM31WrappingMapV1.actual_mul_by_r_eq_ok]
    rfl
  have htargetProbe :
      mapResult AspisR1CurrentWide.Proof.toCM
        (AspisR1CurrentWide.field.mul_by_r (cmToCurrent x)) =
      .ok (AspisR1.R22CanonicalQM31.wrappingByR
        (AspisR1S9ActualQM31WrappingMapV1.toProbeCM x)) := by
    rw [current_mul_by_r_to_probe, probe_cmToCurrent]
    exact AspisR1.R22CanonicalQM31.byR_agrees _ hx
  have hmaps :
      mapResult AspisR1CurrentWide.Proof.toCM
        (mapResult cmToCurrent
          (AspisR1S9ActualQMMulCutV1.field.mul_by_r x)) =
      mapResult AspisR1CurrentWide.Proof.toCM
        (AspisR1CurrentWide.field.mul_by_r (cmToCurrent x)) := by
    calc
      _ = mapResult AspisR1S9ActualQM31WrappingMapV1.toProbeCM
            (AspisR1S9ActualQMMulCutV1.field.mul_by_r x) := currentProbe_comp _
      _ = _ := hsourceProbe.trans htargetProbe.symm
  exact result_map_injective AspisR1CurrentWide.Proof.toCM
    currentProbe_cm_injective _ _ hmaps

/-- The complete qcut `mul_u` expression maps to CurrentWide's actual
`wide_exact.mul_u`, preserving all Result branches. The only semantic seam is
the canonical-input `mul_by_r` bridge above. -/
theorem qcut_mul_u_maps_to_current (x : CutQM)
    (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM x)) :
    mapResult qmToCurrent
      (AspisR1S9WideSourceRecordMapV1.qcutMulUFormula x) =
      AspisR1CurrentWide.field.wide_exact.mul_u (qmToCurrent x) := by
  unfold AspisR1S9WideSourceRecordMapV1.qcutMulUFormula
    AspisR1CurrentWide.field.wide_exact.mul_u
  have hbyr := qcut_mul_by_r_maps_to_current x.c1 hx.2
  apply mapResult_bind_eq
    cmToCurrent qmToCurrent
    (AspisR1S9ActualQMMulCutV1.field.mul_by_r x.c1)
    (AspisR1CurrentWide.field.mul_by_r (cmToCurrent x.c1))
    (fun c => ok ({ c0 := c, c1 := x.c0 } : CutQM))
    (fun c => ok ({ c0 := c, c1 := (qmToCurrent x).c0 } : CurrentQM))
    hbyr
  intro c
  rfl

#print axioms qcut_mul_by_r_maps_to_current
#print axioms qcut_mul_u_maps_to_current

end AspisR1S9WideSourceMulUCurrentV1
