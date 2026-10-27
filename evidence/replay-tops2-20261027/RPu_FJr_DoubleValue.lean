import RPt_FJc_WeightValues
import RPt_FJc_WeightConstants
import RPu_FJd_LoopReference
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_DoubleValue
open Aeneas Aeneas.Std Result
open FJc_WeightQMBridge (SQ)
open FJc_WeightValues (Canon decode)

theorem value (x out : SQ) (cx : Canon x) (run : FIn_WeightsExtract.double x=ok out) :
    Canon out ∧ decode out=FJd_LoopReference.double (decode x) := by
  unfold FIn_WeightsExtract.double at run
  obtain ⟨q,hq,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q1,hq1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have vq := FJc_WeightValues.mul x x q cx cx hq
  have vq1 := FJc_WeightValues.add q q q1 vq.1 vq.1 hq1
  have vo := FJc_WeightValues.sub q1 FIn_WeightsExtract.field.QM31.ONE out vq1.1 FJc_WeightConstants.one.1 run
  refine ⟨vo.1,?_⟩
  rw [vo.2,vq1.2,vq.2,FJc_WeightConstants.one.2]
  rfl

#print axioms value
end AspisR1.FJr_DoubleValue
end
