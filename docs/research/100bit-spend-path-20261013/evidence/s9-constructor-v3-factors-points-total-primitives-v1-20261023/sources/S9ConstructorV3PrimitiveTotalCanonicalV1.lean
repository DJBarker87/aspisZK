import S9ConstructorV3QMMulCanonicalV1
import S9ConstructorV3QMAddSubCanonicalV1
import S9QMMulM31PrimitiveSourceBridgeV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ConstructorV3PrimitiveTotalCanonicalV1
open AspisR1S9ActualWeightsNewBoxNewV3
open AspisR1S9ConstructorV3QMAddSubCanonicalV1

/-- Reflect target success through the complete Result map. No source-success
hypothesis is needed, and source failure/divergence are excluded explicitly. -/
theorem qm_mul_total_canonical (x y : field.QM31)
    (hx : CanQM (toProbeQM x)) (hy : CanQM (toProbeQM y)) :
    ∃ out, field.QM31.mul x y = .ok out ∧ CanQM (toProbeQM out) := by
  obtain ⟨target, htarget, _⟩ :=
    AspisR1S9ActualQM31TotalCanonicalV1.actual_qm_mul_total_canonical
      (AspisR1S9ConstructorV3QMMulCanonicalV1.toActualQM x)
      (AspisR1S9ConstructorV3QMMulCanonicalV1.toActualQM y) hx hy
  have hmap := AspisR1S9ConstructorV3QMMulCanonicalV1.generated_mul_maps_to_cut x y
  rw [htarget] at hmap
  cases hsource : field.QM31.mul x y with
  | ok out =>
    refine ⟨out, rfl, ?_⟩
    exact AspisR1S9ConstructorV3QMMulCanonicalV1.generated_mul_success_canonical x y out hx hy hsource
  | fail e =>
    rw [hsource] at hmap
    change Result.fail e = Result.ok target at hmap
    cases hmap
  | div =>
    rw [hsource] at hmap
    change Result.div = Result.ok target at hmap
    cases hmap

 theorem m31_add_total_canonical (x y : field.M31)
    (hx : x.val < P) (hy : y.val < P) :
    ∃ out, field.M31.add x y = .ok out ∧ out.val < P := by
  have hcall : field.M31.add x y = .ok (AspisR1.R22CanonicalM31AddSub.wrappingAdd x y) :=
    (AspisR1S9ConstructorV3QMMulMapV1.m31_add_same x y).trans
      (AspisR1S9QMMulM31PrimitiveSourceBridgeV1.actual_m31_add_eq_r22_wrapping x y)
  exact ⟨_, hcall, m31_add_success_canonical x y _ hx hy hcall⟩

 theorem cm_add_total_canonical (x y : field.CM31)
    (hx : CanCM (toProbeCM x)) (hy : CanCM (toProbeCM y)) :
    ∃ out, field.CM31.add x y = .ok out ∧ CanCM (toProbeCM out) := by
  obtain ⟨a, ha, _⟩ := m31_add_total_canonical x.a y.a hx.1 hy.1
  obtain ⟨b, hb, _⟩ := m31_add_total_canonical x.b y.b hx.2 hy.2
  have hcall : field.CM31.add x y = .ok (field.CM31.mk a b) := by
    simp only [field.CM31.add, ha, bind_tc_ok, hb]
  exact ⟨_, hcall, cm_add_success_canonical x y _ hx hy hcall⟩

 theorem qm_add_total_canonical (x y : field.QM31)
    (hx : CanQM (toProbeQM x)) (hy : CanQM (toProbeQM y)) :
    ∃ out, field.QM31.add x y = .ok out ∧ CanQM (toProbeQM out) := by
  obtain ⟨a, ha, _⟩ := cm_add_total_canonical x.c0 y.c0 hx.1 hy.1
  obtain ⟨b, hb, _⟩ := cm_add_total_canonical x.c1 y.c1 hx.2 hy.2
  have hcall : field.QM31.add x y = .ok (field.QM31.mk a b) := by
    simp only [field.QM31.add, ha, bind_tc_ok, hb]
  exact ⟨_, hcall, qm_add_success_canonical x y _ hx hy hcall⟩

 theorem m31_sub_total_canonical (x y : field.M31)
    (hx : x.val < P) (hy : y.val < P) :
    ∃ out, field.M31.sub x y = .ok out ∧ out.val < P := by
  have hcall : field.M31.sub x y = .ok (AspisR1.R22CanonicalM31AddSub.wrappingSub x y) :=
    (AspisR1S9ConstructorV3QMMulMapV1.m31_sub_same x y).trans
      (AspisR1S9QMMulM31PrimitiveSourceBridgeV1.actual_m31_sub_eq_r22_wrapping x y)
  exact ⟨_, hcall, m31_sub_success_canonical x y _ hx hy hcall⟩

 theorem cm_sub_total_canonical (x y : field.CM31)
    (hx : CanCM (toProbeCM x)) (hy : CanCM (toProbeCM y)) :
    ∃ out, field.CM31.sub x y = .ok out ∧ CanCM (toProbeCM out) := by
  obtain ⟨a, ha, _⟩ := m31_sub_total_canonical x.a y.a hx.1 hy.1
  obtain ⟨b, hb, _⟩ := m31_sub_total_canonical x.b y.b hx.2 hy.2
  have hcall : field.CM31.sub x y = .ok (field.CM31.mk a b) := by
    simp only [field.CM31.sub, ha, bind_tc_ok, hb]
  exact ⟨_, hcall, cm_sub_success_canonical x y _ hx hy hcall⟩

 theorem qm_sub_total_canonical (x y : field.QM31)
    (hx : CanQM (toProbeQM x)) (hy : CanQM (toProbeQM y)) :
    ∃ out, field.QM31.sub x y = .ok out ∧ CanQM (toProbeQM out) := by
  obtain ⟨a, ha, _⟩ := cm_sub_total_canonical x.c0 y.c0 hx.1 hy.1
  obtain ⟨b, hb, _⟩ := cm_sub_total_canonical x.c1 y.c1 hx.2 hy.2
  have hcall : field.QM31.sub x y = .ok (field.QM31.mk a b) := by
    simp only [field.QM31.sub, ha, bind_tc_ok, hb]
  exact ⟨_, hcall, qm_sub_success_canonical x y _ hx hy hcall⟩

#print axioms qm_mul_total_canonical
#print axioms m31_add_total_canonical
#print axioms cm_add_total_canonical
#print axioms qm_add_total_canonical
#print axioms m31_sub_total_canonical
#print axioms cm_sub_total_canonical
#print axioms qm_sub_total_canonical
end AspisR1S9ConstructorV3PrimitiveTotalCanonicalV1
