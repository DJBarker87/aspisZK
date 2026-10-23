import AspisR1S9ActualWeightsNewBoxNewV3.Funs
import S9ConstructorV3QMMulCanonicalV1
import S9ConstructorV3QMAddSubCanonicalV1
import S9ConstructorV3QMMulMapV1
import S9QMMulM31PrimitiveSourceBridgeV1
import R22CanonicalM31AddSub
import R22CanonicalQM31

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9ConstructorV3DoubleCanonicalV1

abbrev P := AspisR1.ExtractedCurrentTowerAdd.P
abbrev CanCM := AspisR1.ExtractedCurrentTowerAdd.CanonicalCM
abbrev CanQM := AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
abbrev V3QM := AspisR1S9ActualWeightsNewBoxNewV3.field.QM31
abbrev V3CM := AspisR1S9ActualWeightsNewBoxNewV3.field.CM31

def toProbeCM (x : V3CM) : AspisR1S9ActualQM31WrappingMapV1.ProbeCM :=
  ⟨x.a, x.b⟩

def toProbeQM (x : V3QM) : AspisR1S9ActualQM31WrappingMapV1.ProbeQM :=
  AspisR1S9ConstructorV3QMMulCanonicalV1.toProbe x

private theorem one_canonical :
    CanQM (toProbeQM AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE) := by
  change CanQM
    (AspisR1S9ActualQM31WrappingMapV1.toProbeQM
      (AspisR1S9ConstructorV3QMMulCanonicalV1.toActualQM
        AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE))
  simp only [AspisR1S9ActualQM31WrappingMapV1.toProbeQM,
    AspisR1S9ConstructorV3QMMulCanonicalV1.toActualQM,
    AspisR1S9ConstructorV3QMMulCanonicalV1.toActualCM,
    AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE]
  constructor <;> constructor <;> decide

/-- The actual V3 `double` body preserves QM31 canonicality, using only its
same-run multiplication, addition, and subtraction calls and the retained
source arithmetic canonicality lemmas. -/
theorem generated_double_success_canonical
    (x z : V3QM)
    (hx : CanQM (toProbeQM x))
    (hcall : AspisR1S9ActualWeightsNewBoxNewV3.double x = .ok z) :
    CanQM (toProbeQM z) := by
  unfold AspisR1S9ActualWeightsNewBoxNewV3.double at hcall
  cases hm : AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.mul x x with
  | ok q =>
    cases ha : AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.add q q with
    | ok q1 =>
      cases hs : AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.sub q1
          AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE with
      | ok out =>
        simp only [hm, bind_tc_ok, ha, bind_tc_ok, hs, bind_tc_ok] at hcall
        have hout : out = z := Result.ok.inj hcall
        subst z
        have hq := AspisR1S9ConstructorV3QMMulCanonicalV1.generated_mul_success_canonical
          x x q hx hx hm
        have hq1 : CanQM (toProbeQM q1) := by
          simpa only [toProbeQM,
            AspisR1S9ConstructorV3QMAddSubCanonicalV1.toProbeQM] using
            AspisR1S9ConstructorV3QMAddSubCanonicalV1.qm_add_success_canonical
              q q q1 hq hq ha
        have hOne : CanQM (toProbeQM
            AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE) := one_canonical
        simpa only [toProbeQM,
          AspisR1S9ConstructorV3QMAddSubCanonicalV1.toProbeQM] using
          AspisR1S9ConstructorV3QMAddSubCanonicalV1.qm_sub_success_canonical
            q1 AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE out hq1 hOne hs
      | fail e => simp [hm, ha, hs] at hcall
      | div => simp [hm, ha, hs] at hcall
    | fail e => simp [hm, ha] at hcall
    | div => simp [hm, ha] at hcall
  | fail e => simp [hm] at hcall
  | div => simp [hm] at hcall

#print axioms generated_double_success_canonical

end AspisR1S9ConstructorV3DoubleCanonicalV1
