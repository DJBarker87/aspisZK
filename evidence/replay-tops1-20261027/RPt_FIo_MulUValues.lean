import RPt_FIo_QMValues
import RPt_FIo_ByRValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_MulUValues
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NQ qm cm)
open FIo_QMValues (Canon)

theorem value (x z : NQ) (hx : Canon x)
    (run : FIo_Native.aspis_core.field.wide_exact.mul_u x=ok z) :
    Canon z ∧ decodeQM (qm z)=AspisWideTower.wideU*decodeQM (qm x) := by
  unfold FIo_Native.aspis_core.field.wide_exact.mul_u at run
  obtain ⟨r,hr,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same : (⟨r,x.c0⟩ : NQ)=z := Result.ok.inj run
  subst z
  have dr := FIo_ByRValues.value x.c1 r hx.2 hr
  refine ⟨⟨dr.1,hx.1⟩,?_⟩
  apply QuadraticAlgebra.ext
  · simpa [decodeQM,AspisR1.ExtractedCurrentQM31Exact.decode,toQM,toCM,
      decodeC,decodeM,qm,cm,AspisWideTower.wideU,mul_comm] using dr.2
  · simp [decodeQM,AspisR1.ExtractedCurrentQM31Exact.decode,toQM,toCM,
      decodeC,decodeM,qm,cm,AspisWideTower.wideU]

#print axioms value
end AspisR1.FIo_MulUValues
end
