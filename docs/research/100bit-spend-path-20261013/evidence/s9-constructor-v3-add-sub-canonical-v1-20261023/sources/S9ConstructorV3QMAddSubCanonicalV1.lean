import AspisR1S9ActualWeightsNewBoxNewV3.Funs
import S9ConstructorV3QMMulCanonicalV1
import S9ConstructorV3QMMulMapV1
import S9QMMulM31PrimitiveSourceBridgeV1
import R22CanonicalM31AddSub

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9ConstructorV3QMAddSubCanonicalV1

abbrev P := AspisR1.ExtractedCurrentTowerAdd.P
abbrev CanCM := AspisR1.ExtractedCurrentTowerAdd.CanonicalCM
abbrev CanQM := AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
abbrev V3QM := AspisR1S9ActualWeightsNewBoxNewV3.field.QM31
abbrev V3CM := AspisR1S9ActualWeightsNewBoxNewV3.field.CM31

def toProbeCM (x : V3CM) : AspisR1S9ActualQM31WrappingMapV1.ProbeCM :=
  ⟨x.a, x.b⟩

def toProbeQM (x : V3QM) : AspisR1S9ActualQM31WrappingMapV1.ProbeQM :=
  AspisR1S9ConstructorV3QMMulCanonicalV1.toProbe x

theorem m31_add_success_canonical
    (x y z : AspisR1S9ActualWeightsNewBoxNewV3.field.M31)
    (hx : x.val < P) (hy : y.val < P)
    (hcall : AspisR1S9ActualWeightsNewBoxNewV3.field.M31.add x y = .ok z) :
    z.val < P := by
  have hsame := AspisR1S9ConstructorV3QMMulMapV1.m31_add_same x y
  have hcut := hsame.symm.trans hcall
  have hwrap := AspisR1S9QMMulM31PrimitiveSourceBridgeV1.actual_m31_add_eq_r22_wrapping x y
  have hz : z = AspisR1.R22CanonicalM31AddSub.wrappingAdd x y :=
    Result.ok.inj (hcut.symm.trans hwrap)
  rw [hz]
  exact AspisR1.R22CanonicalM31AddSub.wrapping_add_canonical x y hx hy

theorem m31_sub_success_canonical
    (x y z : AspisR1S9ActualWeightsNewBoxNewV3.field.M31)
    (hx : x.val < P) (hy : y.val < P)
    (hcall : AspisR1S9ActualWeightsNewBoxNewV3.field.M31.sub x y = .ok z) :
    z.val < P := by
  have hsame := AspisR1S9ConstructorV3QMMulMapV1.m31_sub_same x y
  have hcut := hsame.symm.trans hcall
  have hwrap := AspisR1S9QMMulM31PrimitiveSourceBridgeV1.actual_m31_sub_eq_r22_wrapping x y
  have hz : z = AspisR1.R22CanonicalM31AddSub.wrappingSub x y :=
    Result.ok.inj (hcut.symm.trans hwrap)
  rw [hz]
  exact AspisR1.R22CanonicalM31AddSub.wrapping_sub_canonical x y hx hy

theorem cm_add_success_canonical
    (x y z : V3CM)
    (hx : CanCM (toProbeCM x)) (hy : CanCM (toProbeCM y))
    (hcall : AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.add x y = .ok z) :
    CanCM (toProbeCM z) := by
  unfold AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.add at hcall
  cases h0 : AspisR1S9ActualWeightsNewBoxNewV3.field.M31.add x.a y.a with
  | ok a =>
    cases h1 : AspisR1S9ActualWeightsNewBoxNewV3.field.M31.add x.b y.b with
    | ok b =>
      simp only [h0, bind_tc_ok, h1, bind_tc_ok] at hcall
      have hz : z = ⟨a, b⟩ := (Result.ok.inj hcall).symm
      subst z
      exact ⟨m31_add_success_canonical x.a y.a a hx.1 hy.1 h0,
        m31_add_success_canonical x.b y.b b hx.2 hy.2 h1⟩
    | fail e => simp [h0, h1] at hcall
    | div => simp [h0, h1] at hcall
  | fail e => simp [h0] at hcall
  | div => simp [h0] at hcall

theorem cm_sub_success_canonical
    (x y z : V3CM)
    (hx : CanCM (toProbeCM x)) (hy : CanCM (toProbeCM y))
    (hcall : AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.sub x y = .ok z) :
    CanCM (toProbeCM z) := by
  unfold AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.sub at hcall
  cases h0 : AspisR1S9ActualWeightsNewBoxNewV3.field.M31.sub x.a y.a with
  | ok a =>
    cases h1 : AspisR1S9ActualWeightsNewBoxNewV3.field.M31.sub x.b y.b with
    | ok b =>
      simp only [h0, bind_tc_ok, h1, bind_tc_ok] at hcall
      have hz : z = ⟨a, b⟩ := (Result.ok.inj hcall).symm
      subst z
      exact ⟨m31_sub_success_canonical x.a y.a a hx.1 hy.1 h0,
        m31_sub_success_canonical x.b y.b b hx.2 hy.2 h1⟩
    | fail e => simp [h0, h1] at hcall
    | div => simp [h0, h1] at hcall
  | fail e => simp [h0] at hcall
  | div => simp [h0] at hcall

theorem qm_add_success_canonical
    (x y z : V3QM)
    (hx : CanQM (toProbeQM x)) (hy : CanQM (toProbeQM y))
    (hcall : AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.add x y = .ok z) :
    CanQM (toProbeQM z) := by
  unfold AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.add at hcall
  cases h0 : AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.add x.c0 y.c0 with
  | ok a =>
    cases h1 : AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.add x.c1 y.c1 with
    | ok b =>
      simp only [h0, bind_tc_ok, h1, bind_tc_ok] at hcall
      have hz : z = ⟨a, b⟩ := (Result.ok.inj hcall).symm
      subst z
      exact ⟨cm_add_success_canonical x.c0 y.c0 a hx.1 hy.1 h0,
        cm_add_success_canonical x.c1 y.c1 b hx.2 hy.2 h1⟩
    | fail e => simp [h0, h1] at hcall
    | div => simp [h0, h1] at hcall
  | fail e => simp [h0] at hcall
  | div => simp [h0] at hcall

theorem qm_sub_success_canonical
    (x y z : V3QM)
    (hx : CanQM (toProbeQM x)) (hy : CanQM (toProbeQM y))
    (hcall : AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.sub x y = .ok z) :
    CanQM (toProbeQM z) := by
  unfold AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.sub at hcall
  cases h0 : AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.sub x.c0 y.c0 with
  | ok a =>
    cases h1 : AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.sub x.c1 y.c1 with
    | ok b =>
      simp only [h0, bind_tc_ok, h1, bind_tc_ok] at hcall
      have hz : z = ⟨a, b⟩ := (Result.ok.inj hcall).symm
      subst z
      exact ⟨cm_sub_success_canonical x.c0 y.c0 a hx.1 hy.1 h0,
        cm_sub_success_canonical x.c1 y.c1 b hx.2 hy.2 h1⟩
    | fail e => simp [h0, h1] at hcall
    | div => simp [h0, h1] at hcall
  | fail e => simp [h0] at hcall
  | div => simp [h0] at hcall

#print axioms qm_add_success_canonical
#print axioms qm_sub_success_canonical

end AspisR1S9ConstructorV3QMAddSubCanonicalV1
