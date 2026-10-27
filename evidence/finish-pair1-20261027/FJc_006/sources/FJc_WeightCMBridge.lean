import FJc_WeightScalarBridge
set_option autoImplicit false
namespace AspisR1.FJc_WeightCMBridge
open Aeneas Aeneas.Std Result
abbrev SC := FIn_WeightsExtract.field.CM31
abbrev NC := FIo_Native.aspis_core.field.CM31
def toC (x : SC) : NC := ⟨x.a,x.b⟩

theorem add (x y z : SC) (run : FIn_WeightsExtract.field.CM31.add x y=ok z) :
    FIo_Native.aspis_core.field.CM31.add (toC x) (toC y)=ok (toC z) := by
  unfold FIn_WeightsExtract.field.CM31.add at run
  obtain ⟨a,ha,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases Result.ok.inj run
  unfold FIo_Native.aspis_core.field.CM31.add
  simp only [toC,←FJc_WeightScalarBridge.add,ha,hb,bind_tc_ok]

theorem sub (x y z : SC) (run : FIn_WeightsExtract.field.CM31.sub x y=ok z) :
    FIo_Native.aspis_core.field.CM31.sub (toC x) (toC y)=ok (toC z) := by
  unfold FIn_WeightsExtract.field.CM31.sub at run
  obtain ⟨a,ha,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases Result.ok.inj run
  unfold FIo_Native.aspis_core.field.CM31.sub
  simp only [toC,←FJc_WeightScalarBridge.sub,ha,hb,bind_tc_ok]

#print axioms add
#print axioms sub
end AspisR1.FJc_WeightCMBridge
