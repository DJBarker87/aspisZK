import FIo_WideMulValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_ScaleValues
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NC NQ NE cm qm wide)

theorem cm_scale (x z : NC) (y : U32)
    (run : FIo_Native.aspis_core.field.CM31.mul_m31 x y=ok z) :
    FIo_CMValues.Canon z ∧ decodeC (cm z)=decodeM y • decodeC (cm x) := by
  unfold FIo_Native.aspis_core.field.CM31.mul_m31 at run
  obtain ⟨a,ha,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same : (⟨a,b⟩ : NC)=z := Result.ok.inj run
  subst z
  have va := FIo_M31Values.mul x.a y a ha
  have vb := FIo_M31Values.mul x.b y b hb
  refine ⟨⟨va.1,vb.1⟩,?_⟩
  apply QuadraticAlgebra.ext
  · simpa [decodeC,cm,smul_eq_mul,mul_comm] using va.2
  · simpa [decodeC,cm,smul_eq_mul,mul_comm] using vb.2

theorem qm_scale (x z : NQ) (y : U32)
    (run : FIo_Native.aspis_core.field.QM31.mul_m31 x y=ok z) :
    FIo_QMValues.Canon z := by
  unfold FIo_Native.aspis_core.field.QM31.mul_m31 at run
  obtain ⟨a,ha,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same : (⟨a,b⟩ : NQ)=z := Result.ok.inj run
  subst z
  exact ⟨(cm_scale x.c0 a y ha).1,(cm_scale x.c1 b y hb).1⟩

theorem wide_scale (x z : NE) (y : U32)
    (run : FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 x y=ok z) :
    FIo_WideValues.Canon z := by
  unfold FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 at run
  obtain ⟨scalar,hscalar,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨a,ha,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same : (⟨a,b⟩ : NE)=z := Result.ok.inj run
  subst z
  exact ⟨qm_scale x.c0 a scalar ha,qm_scale x.c1 b scalar hb⟩

#print axioms cm_scale
#print axioms qm_scale
#print axioms wide_scale
end AspisR1.FIo_ScaleValues
end
