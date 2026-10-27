import FJd_LoopReference
import FJc_WeightConstants
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJd_SourceDouble
open Aeneas Aeneas.Std Result
open FJc_WeightQMBridge (SQ)
open FJc_WeightValues
/-- Actual straight-line double body; no circle loop is unfolded. -/
theorem value (x y : SQ) (hx : Canon x)
    (run : FIn_WeightsExtract.double x=ok y) :
    Canon y ∧ decode y=FJd_LoopReference.double (decode x) := by
  unfold FIn_WeightsExtract.double at run
  obtain ⟨xx,hxx,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨twice,ht,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have hxx' := FJc_WeightValues.mul _ _ _ hx hx hxx
  have ht' := FJc_WeightValues.add _ _ _ hxx'.1 hxx'.1 ht
  have hy := FJc_WeightValues.sub _ _ _ ht'.1 FJc_WeightConstants.one.1 run
  exact ⟨hy.1,by rw [hy.2,ht'.2,hxx'.2,FJc_WeightConstants.one.2];rfl⟩
#print axioms value
end AspisR1.FJd_SourceDouble
end
