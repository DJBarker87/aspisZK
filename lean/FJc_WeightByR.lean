import FJc_WeightCMMul
set_option autoImplicit false
namespace AspisR1.FJc_WeightByR
open Aeneas Aeneas.Std Result
open FJc_WeightCMBridge (SC toC)
theorem value (x z : SC) (run : FIn_WeightsExtract.field.mul_by_r x=ok z) :
    FIo_Native.aspis_core.field.mul_by_r (toC x)=ok (toC z) := by
  unfold FIn_WeightsExtract.field.mul_by_r at run
  simp only [FJc_WeightScalarBridge.double,FJc_WeightScalarBridge.sub,FJc_WeightScalarBridge.add] at run
  obtain ⟨a,ha,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨c,hc,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨d,hd,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases Result.ok.inj run
  unfold FIo_Native.aspis_core.field.mul_by_r
  simp only [toC,ha,hb,hc,hd,bind_tc_ok]
#print axioms value
end AspisR1.FJc_WeightByR
