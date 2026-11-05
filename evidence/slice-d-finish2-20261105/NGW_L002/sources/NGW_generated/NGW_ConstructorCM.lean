import NGM_ProbeTransport
set_option autoImplicit false
noncomputable section
namespace NGW_ConstructorCM
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
abbrev C := FIn_WeightsExtract.field.CM31
def Canon (x : C) : Prop := x.a.val<2147483647 ∧ x.b.val<2147483647
theorem add (x y : C) (hx : Canon x) (hy : Canon y) :
    ∃ z,FIn_WeightsExtract.field.CM31.add x y=ok z ∧ Canon z := by
  obtain ⟨a,ha,_,ca⟩ := LPi_NatBase.add x.a y.a hx.1 hy.1
  obtain ⟨b,hb,_,cb⟩ := LPi_NatBase.add x.b y.b hx.2 hy.2
  refine ⟨⟨a,b⟩,?_,⟨ca,cb⟩⟩
  simp only [FIn_WeightsExtract.field.CM31.add,NGM_ProbeTransport.base_add,ha,hb,bind_tc_ok]

theorem sub (x y : C) (hx : Canon x) (hy : Canon y) :
    ∃ z,FIn_WeightsExtract.field.CM31.sub x y=ok z ∧ Canon z := by
  obtain ⟨a,ha,_,ca⟩ := LPi_NatBase.sub x.a y.a hx.1 hy.1
  obtain ⟨b,hb,_,cb⟩ := LPi_NatBase.sub x.b y.b hx.2 hy.2
  refine ⟨⟨a,b⟩,?_,⟨ca,cb⟩⟩
  simp only [FIn_WeightsExtract.field.CM31.sub,NGM_ProbeTransport.base_sub,ha,hb,bind_tc_ok]

theorem mul (x y : C) (hx : Canon x) (hy : Canon y) :
    ∃ z,FIn_WeightsExtract.field.CM31.mul x y=ok z ∧ Canon z := by
  obtain ⟨z,run,canonical,_⟩ := LPi_FieldValues.cm_mul (NGM_ProbeTransport.toC x) (NGM_ProbeTransport.toC y) hx hy
  have bridge := NGM_ProbeTransport.cm_mul x y
  rw [run] at bridge
  obtain ⟨v,hv,hz⟩ := AspisR1.Port3_PushFrame.bind_success _ _ _ bridge
  have eq : NGM_ProbeTransport.toC v = z := Result.ok.inj hz
  exact ⟨v,hv,by simpa only [←eq,NGM_ProbeTransport.toC] using canonical⟩

theorem by_r (x : C) (hx : Canon x) :
    ∃ z,FIn_WeightsExtract.field.mul_by_r x=ok z ∧ Canon z := by
  obtain ⟨a,ha,_,ca⟩ := LPi_NatBase.add x.a x.a hx.1 hx.1
  obtain ⟨b,hb,_,cb⟩ := LPi_NatBase.sub a x.b ca hx.2
  obtain ⟨c,hc,_,cc⟩ := LPi_NatBase.add x.b x.b hx.2 hx.2
  obtain ⟨d,hd,_,cd⟩ := LPi_NatBase.add x.a c hx.1 cc
  refine ⟨⟨b,d⟩,?_,⟨cb,cd⟩⟩
  simp only [FIn_WeightsExtract.field.mul_by_r,FIn_WeightsExtract.field.M31.double,
    NGM_ProbeTransport.base_add,NGM_ProbeTransport.base_sub,ha,hb,hc,hd,bind_tc_ok]

#print axioms add
#print axioms sub
#print axioms mul
#print axioms by_r
end NGW_ConstructorCM
