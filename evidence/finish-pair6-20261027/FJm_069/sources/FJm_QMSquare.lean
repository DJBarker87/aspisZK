import FJm_CMSquare
import FIo_QMMulValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_QMSquare
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NQ qm cm)
attribute [local irreducible] QuadraticAlgebra.instInv

theorem value (x out : NQ) (hx : FIo_QMValues.Canon x)
    (run : FIo_Native.aspis_core.field.QM31.square x=ok out) :
    FIo_QMValues.Canon out ∧ decodeQM (qm out)=decodeQM (qm x)*decodeQM (qm x) := by
  unfold FIo_Native.aspis_core.field.QM31.square at run
  obtain ⟨a,ha,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨r,hr,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨lo,hlo,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨ab,hab,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨hi,hhi,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases Result.ok.inj run
  have va := FJm_CMSquare.value x.c0 a hx.1 ha
  have vb := FJm_CMSquare.value x.c1 b hx.2 hb
  have vr := FIo_ByRValues.value b r vb.1 hr
  have vl := FIo_CMValues.add a r lo va.1 vr.1 hlo
  have vab := FIo_CMMulValues.mul x.c0 x.c1 ab hx.1 hx.2 hab
  change FIo_Native.aspis_core.field.CM31.add ab ab=ok hi at hhi
  have vh := FIo_CMValues.add ab ab hi vab.1 vab.1 hhi
  refine ⟨⟨vl.1,vh.1⟩,?_⟩
  apply QuadraticAlgebra.ext
  · simp only [decodeQM,qm,QuadraticAlgebra.re_mul]
    rw [vl.2,vr.2,va.2,vb.2]
    ring
  · simp only [decodeQM,qm,QuadraticAlgebra.im_mul,zero_mul,zero_add,add_zero]
    rw [vh.2,vab.2]
    ring
#print axioms value
end AspisR1.FJm_QMSquare
end
