import RPt_FJc_WeightCMBridge
set_option autoImplicit false
namespace AspisR1.FJc_WeightCMMul
open Aeneas Aeneas.Std Result
open FJc_WeightCMBridge (SC toC)
theorem mul (x y z : SC) (run : FIn_WeightsExtract.field.CM31.mul x y=ok z) :
    FIo_Native.aspis_core.field.CM31.mul (toC x) (toC y)=ok (toC z) := by
  unfold FIn_WeightsExtract.field.CM31.mul at run
  simp only [lift,bind_tc_ok,FIn_WeightsExtract.field.M31.reduce_u64,
    FJc_WeightScalarBridge.mul,FJc_WeightScalarBridge.sub,FJc_WeightScalarBridge.reduce] at run
  obtain ⟨a,ha,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨c,hc,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨d,hd,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨e,he,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨f,hf,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases Result.ok.inj run
  unfold FIo_Native.aspis_core.field.CM31.mul
  simp only [toC,lift,bind_tc_ok,ha,hb,FIo_Native.aspis_core.field.M31.reduce_u64,hc,hd,he,hf]
#print axioms mul
end AspisR1.FJc_WeightCMMul
