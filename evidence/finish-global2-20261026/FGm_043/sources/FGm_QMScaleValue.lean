import FIo_ScaleValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FGm_QMScaleValue
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NC NQ NE cm qm wide)

theorem value (x z : NQ) (y : U32)
    (run : FIo_Native.aspis_core.field.QM31.mul_m31 x y=ok z) :
    FIo_QMValues.Canon z ∧ decodeQM (qm z)=decodeM y • decodeQM (qm x) := by
  unfold FIo_Native.aspis_core.field.QM31.mul_m31 at run
  obtain ⟨a,ha,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same : (⟨a,b⟩ : NQ)=z := Result.ok.inj run
  subst z
  have va := FIo_ScaleValues.cm_scale x.c0 a y ha
  have vb := FIo_ScaleValues.cm_scale x.c1 b y hb
  refine ⟨⟨va.1,vb.1⟩,?_⟩
  apply QuadraticAlgebra.ext
  · exact va.2
  · exact vb.2

#print axioms value
end AspisR1.FGm_QMScaleValue
end
