import RPu_FIo_CanonicalQM
import RPt_FIo_WideMulValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_MixedValues
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NE NQ wide qm)

theorem mul_qm (x z : NE) (y : NQ) (hx : FIo_WideValues.Canon x)
    (run : FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31 x y=ok z) :
    FIo_WideValues.Canon z ∧ decodeWide (wide z)=decodeWide (wide x)*
      algebraMap OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E (decodeQM (qm y)) := by
  unfold FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31 at run
  obtain ⟨rhs,hrhs,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨a,ha,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same : (⟨a,b⟩ : NE)=z := Result.ok.inj run
  subst z
  have vr := FIo_CanonicalQM.value y rhs hrhs
  have va := FIo_QMMulValues.mul x.c0 rhs a hx.1 vr.1 ha
  have vb := FIo_QMMulValues.mul x.c1 rhs b hx.2 vr.1 hb
  refine ⟨⟨va.1,vb.1⟩,?_⟩
  apply QuadraticAlgebra.ext
  · simpa [decodeWide,wide,QuadraticAlgebra.re_mul,vr.2] using va.2
  · simpa [decodeWide,wide,QuadraticAlgebra.im_mul,vr.2] using vb.2

#print axioms mul_qm
end AspisR1.FIo_MixedValues
end
