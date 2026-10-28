import FJc_WeightScalarBridge
import NCJ_CallLog
set_option autoImplicit false
noncomputable section
namespace NCJ_ConstructorCM
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
abbrev C := FIn_WeightsExtract.field.CM31

def Canon (x : C) : Prop := x.a.val<2147483647 ∧ x.b.val<2147483647
def native (x : C) : NC := ⟨x.a,x.b⟩

theorem add (x y : C) (hx : Canon x) (hy : Canon y) :
    ∃ z,FIn_WeightsExtract.field.CM31.add x y=ok z ∧ Canon z := by
  obtain ⟨a,ha,_,ca⟩ := LPi_NatBase.add x.a y.a hx.1 hy.1
  obtain ⟨b,hb,_,cb⟩ := LPi_NatBase.add x.b y.b hx.2 hy.2
  refine ⟨⟨a,b⟩,?_,⟨ca,cb⟩⟩
  simp only [FIn_WeightsExtract.field.CM31.add,FJc_WeightScalarBridge.add,ha,hb,bind_tc_ok]

theorem sub (x y : C) (hx : Canon x) (hy : Canon y) :
    ∃ z,FIn_WeightsExtract.field.CM31.sub x y=ok z ∧ Canon z := by
  obtain ⟨a,ha,_,ca⟩ := LPi_NatBase.sub x.a y.a hx.1 hy.1
  obtain ⟨b,hb,_,cb⟩ := LPi_NatBase.sub x.b y.b hx.2 hy.2
  refine ⟨⟨a,b⟩,?_,⟨ca,cb⟩⟩
  simp only [FIn_WeightsExtract.field.CM31.sub,FJc_WeightScalarBridge.sub,ha,hb,bind_tc_ok]

/-- Total canonical arithmetic on the constructor's actual distinct carrier,
using the proved native scalar operations. No successful operation is assumed. -/
theorem mul (x y : C) (hx : Canon x) (hy : Canon y) :
    ∃ z,FIn_WeightsExtract.field.CM31.mul x y=ok z ∧ Canon z := by
  obtain ⟨z,run,canonical,_⟩ := LPi_FieldValues.cm_mul (native x) (native y) hx hy
  unfold FIo_Native.aspis_core.field.CM31.mul at run
  simp only [native,lift,bind_tc_ok,FIo_Native.aspis_core.field.M31.reduce_u64] at run
  obtain ⟨a,ha,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨c,hc,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨d,hd,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨e,he,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨f,hf,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases Result.ok.inj run
  refine ⟨⟨d,f⟩,?_,canonical⟩
  simp only [FIn_WeightsExtract.field.CM31.mul,FIn_WeightsExtract.field.M31.reduce_u64,
    FJc_WeightScalarBridge.mul,FJc_WeightScalarBridge.sub,FJc_WeightScalarBridge.reduce,
    lift,bind_tc_ok,ha,hb,hc,hd,he,hf]

theorem by_r (x : C) (hx : Canon x) :
    ∃ z,FIn_WeightsExtract.field.mul_by_r x=ok z ∧ Canon z := by
  obtain ⟨a,ha,_,ca⟩ := LPi_NatBase.add x.a x.a hx.1 hx.1
  obtain ⟨b,hb,_,cb⟩ := LPi_NatBase.sub a x.b ca hx.2
  obtain ⟨c,hc,_,cc⟩ := LPi_NatBase.add x.b x.b hx.2 hx.2
  obtain ⟨d,hd,_,cd⟩ := LPi_NatBase.add x.a c hx.1 cc
  refine ⟨⟨b,d⟩,?_,⟨cb,cd⟩⟩
  simp only [FIn_WeightsExtract.field.mul_by_r,FIn_WeightsExtract.field.M31.double,
    FJc_WeightScalarBridge.add,FJc_WeightScalarBridge.sub,ha,hb,hc,hd,bind_tc_ok]

#print axioms add
#print axioms sub
#print axioms mul
#print axioms by_r
end NCJ_ConstructorCM
