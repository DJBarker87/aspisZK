import S9ActualQM31CanonicalCheckedMapV1
import S9ActualQM31TotalCanonicalV1
import CurrentWideQMBridge
import KpowersCurrentQMSemanticsV1
import S3S9ConcreteFieldOpsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9ActualQMCurrentHelperMapV1

abbrev ActualQM := AspisR1S9ActualQMMulCutV1.field.QM31
abbrev CurrentQM := AspisR1CurrentWide.field.QM31
abbrev HelperQM := AspisR1S9HelperP6.field.QM31

def mapResult {A B : Type} (f : A → B) : Result A → Result B
  | .ok x => .ok (f x)
  | .fail e => .fail e
  | .div => .div

theorem mapResult_eq_bind {A B : Type} (f : A → B) (r : Result A) :
    mapResult f r = (do
      let x ← r
      Result.ok (f x)) := by
  cases r <;> rfl

/-- Representation bridge from the source cut carrier to CurrentWide. -/
def actualToCurrent (x : ActualQM) : CurrentQM :=
  ⟨⟨x.c0.a, x.c0.b⟩, ⟨x.c1.a, x.c1.b⟩⟩

def actualToHelper (x : ActualQM) : HelperQM :=
  AspisR1S9HelperP6PowerSemanticsV1.currentToHelperQM (actualToCurrent x)

theorem probe_actualToCurrent (x : ActualQM) :
    AspisR1CurrentWide.Proof.toQM (actualToCurrent x) =
      AspisR1S9ActualQM31WrappingMapV1.toProbeQM x := by
  cases x
  rfl

theorem currentProbe_injective (x y : CurrentQM)
    (h : AspisR1CurrentWide.Proof.toQM x = AspisR1CurrentWide.Proof.toQM y) : x = y := by
  have h00 : x.c0.a = y.c0.a := congrArg (fun z : AspisR1Qm31ArithmeticProbe.field.QM31 => z.c0.a) h
  have h01 : x.c0.b = y.c0.b := congrArg (fun z : AspisR1Qm31ArithmeticProbe.field.QM31 => z.c0.b) h
  have h10 : x.c1.a = y.c1.a := congrArg (fun z : AspisR1Qm31ArithmeticProbe.field.QM31 => z.c1.a) h
  have h11 : x.c1.b = y.c1.b := congrArg (fun z : AspisR1Qm31ArithmeticProbe.field.QM31 => z.c1.b) h
  cases x with
  | mk x0 x1 =>
    cases y with
    | mk y0 y1 =>
      cases x0 with
      | mk xa xb =>
        cases y0 with
        | mk ya yb =>
          cases x1 with
          | mk xc xd =>
            cases y1 with
            | mk yc yd =>
              simp only [AspisR1CurrentWide.Proof.toQM,
                AspisR1CurrentWide.Proof.toCM] at h00 h01 h10 h11
              cases h00
              cases h01
              cases h10
              cases h11
              rfl

/-- The actual extracted multiplication, mapped through CurrentWide into the
installed helper carrier, is the same full Result as the concrete helper
`qmMul`. Canonicality is required only at the checked-current seam. -/
theorem actual_qm_mul_maps_to_concrete_helper
    (x y : ActualQM)
    (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM x))
    (hy : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM y)) :
    mapResult actualToHelper
        (AspisR1S9ActualQMMulCutV1.field.QM31.mul x y) =
      @AspisR1S9HelperP6.FieldOps.qmMul
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (actualToHelper x) (actualToHelper y) := by
  let cx := actualToCurrent x
  let cy := actualToCurrent y
  have hactual := AspisR1S9ActualQM31CanonicalCheckedMapV1.actual_qm_mul_eq_checked x y hx hy
  have hcurrent := AspisR1CurrentWide.Proof.qm_mul_same cx cy
  have hinx : AspisR1CurrentWide.Proof.toQM cx =
      AspisR1S9ActualQM31WrappingMapV1.toProbeQM x := by
    exact probe_actualToCurrent x
  have hiny : AspisR1CurrentWide.Proof.toQM cy =
      AspisR1S9ActualQM31WrappingMapV1.toProbeQM y := by
    exact probe_actualToCurrent y
  have hsame :
      mapResult AspisR1S9ActualQM31WrappingMapV1.toProbeQM
          (AspisR1S9ActualQMMulCutV1.field.QM31.mul x y) =
        mapResult AspisR1CurrentWide.Proof.toQM
          (AspisR1CurrentWide.field.QM31.mul cx cy) := by
    calc
      mapResult AspisR1S9ActualQM31WrappingMapV1.toProbeQM
          (AspisR1S9ActualQMMulCutV1.field.QM31.mul x y) =
        (do
          let z ← AspisR1S9ActualQMMulCutV1.field.QM31.mul x y
          Result.ok (AspisR1S9ActualQM31WrappingMapV1.toProbeQM z)) :=
            mapResult_eq_bind _ _
      _ = AspisR1Qm31ArithmeticProbe.field.QM31.mul
            (AspisR1S9ActualQM31WrappingMapV1.toProbeQM x)
            (AspisR1S9ActualQM31WrappingMapV1.toProbeQM y) := hactual
      _ = (do
          let z ← AspisR1CurrentWide.field.QM31.mul cx cy
          Result.ok (AspisR1CurrentWide.Proof.toQM z)) := hcurrent.symm
      _ = mapResult AspisR1CurrentWide.Proof.toQM
            (AspisR1CurrentWide.field.QM31.mul cx cy) := (mapResult_eq_bind _ _).symm
  have hresult :
      mapResult actualToHelper
          (AspisR1S9ActualQMMulCutV1.field.QM31.mul x y) =
        mapResult AspisR1S9HelperP6PowerSemanticsV1.currentToHelperQM
          (AspisR1CurrentWide.field.QM31.mul cx cy) := by
    have htransport :
        mapResult actualToCurrent
            (AspisR1S9ActualQMMulCutV1.field.QM31.mul x y) =
          AspisR1CurrentWide.field.QM31.mul cx cy := by
      cases ha : AspisR1S9ActualQMMulCutV1.field.QM31.mul x y with
      | fail e =>
          cases hc : AspisR1CurrentWide.field.QM31.mul cx cy with
          | fail e' =>
              simp only [ha, hc, mapResult] at hsame ⊢
              cases hsame
              rfl
          | div =>
              simp only [ha, hc, mapResult] at hsame
              cases hsame
          | ok w =>
              simp only [ha, hc, mapResult] at hsame
              cases hsame
      | div =>
          cases hc : AspisR1CurrentWide.field.QM31.mul cx cy with
          | fail e' =>
              simp only [ha, hc, mapResult] at hsame
              cases hsame
          | div =>
              simp only [ha, hc, mapResult] at hsame ⊢
          | ok w =>
              simp only [ha, hc, mapResult] at hsame
              cases hsame
      | ok z =>
          cases hc : AspisR1CurrentWide.field.QM31.mul cx cy with
          | fail e' =>
              simp only [ha, hc, mapResult] at hsame
              cases hsame
          | div =>
              simp only [ha, hc, mapResult] at hsame
              cases hsame
          | ok w =>
              simp only [ha, hc, mapResult] at hsame
              have hout : AspisR1S9ActualQM31WrappingMapV1.toProbeQM z =
                  AspisR1CurrentWide.Proof.toQM w := by
                exact Result.ok.inj hsame
              have hout' : AspisR1CurrentWide.Proof.toQM (actualToCurrent z) =
                  AspisR1CurrentWide.Proof.toQM w := by
                rw [probe_actualToCurrent]
                exact hout
              have hz : actualToCurrent z = w := currentProbe_injective _ _ hout'
              simp only [mapResult, ha, hc]
              rw [hz]
    have hcompose : ∀ r : Result ActualQM,
        mapResult AspisR1S9HelperP6PowerSemanticsV1.currentToHelperQM
            (mapResult actualToCurrent r) =
          mapResult (fun z =>
            AspisR1S9HelperP6PowerSemanticsV1.currentToHelperQM (actualToCurrent z)) r := by
      intro r
      cases r <;> rfl
    calc
      mapResult actualToHelper
          (AspisR1S9ActualQMMulCutV1.field.QM31.mul x y) =
        mapResult (fun z =>
          AspisR1S9HelperP6PowerSemanticsV1.currentToHelperQM (actualToCurrent z))
          (AspisR1S9ActualQMMulCutV1.field.QM31.mul x y) := rfl
      _ = mapResult AspisR1S9HelperP6PowerSemanticsV1.currentToHelperQM
            (mapResult actualToCurrent
              (AspisR1S9ActualQMMulCutV1.field.QM31.mul x y)) :=
          (hcompose _).symm
      _ = mapResult AspisR1S9HelperP6PowerSemanticsV1.currentToHelperQM
            (AspisR1CurrentWide.field.QM31.mul cx cy) := congrArg _ htransport

  calc
    mapResult actualToHelper
        (AspisR1S9ActualQMMulCutV1.field.QM31.mul x y) =
      mapResult AspisR1S9HelperP6PowerSemanticsV1.currentToHelperQM
        (AspisR1CurrentWide.field.QM31.mul cx cy) := hresult
    _ = @AspisR1S9HelperP6.FieldOps.qmMul
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (actualToHelper x) (actualToHelper y) := by
      rw [AspisR1S9ConcreteFieldOpsV1.concrete_qmMul_is_current]
      rw [AspisR1S9HelperP6PowerSemanticsV1.currentQMSemantics_mul_installs_operation]
      simp only [cx, cy, actualToHelper,
        AspisR1S9HelperP6PowerSemanticsV1.helperToCurrent_currentToHelper]
      rw [← mapResult_eq_bind]

#print axioms actual_qm_mul_maps_to_concrete_helper

end AspisR1S9ActualQMCurrentHelperMapV1
