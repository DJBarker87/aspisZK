import R1Z.PV_RunJoin_NativePowerQM66
import PV_B1_FieldWideTotal
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NativePowerCarrier66
open Aeneas Aeneas.Std Result PV_B1_254
abbrev W := aspis_core.field.wide_exact.WideExact
def toS (x : W) : AspisR1ProducerRelease47.field.wide_exact.WideExact :=
  ⟨PV_RunJoin_NativePowerQM66.toQ x.c0,PV_RunJoin_NativePowerQM66.toQ x.c1⟩
theorem mul_u (a : PV_B1_254.aspis_core.field.QM31) : ∃ z,
    aspis_core.field.wide_exact.mul_u a=ok z ∧
    AspisR1ProducerRelease47.field.wide_exact.mul_u (PV_RunJoin_NativePowerQM66.toQ a)=ok (toS z) := by
  obtain ⟨c,hc,ohc⟩ := PV_B1_FieldCM31Total.mul_by_r a.c1
  refine ⟨⟨c,a.c0⟩,?_,?_⟩
  · simp only [aspis_core.field.wide_exact.mul_u,hc,bind_tc_ok]
  · simp only [toS,AspisR1ProducerRelease47.field.wide_exact.mul_u,ohc,bind_tc_ok]
#print axioms mul_u
theorem mul (a b : W) : ∃ z,
    aspis_core.field.wide_exact.WideExact.mul a b=ok z ∧
    AspisR1ProducerRelease47.field.wide_exact.WideExact.mul (toS a) (toS b)=ok (toS z) := by
  obtain ⟨ac,hac,ohac⟩ := PV_RunJoin_NativePowerQM66.mul a.c0 b.c0
  obtain ⟨bd,hbd,ohbd⟩ := PV_RunJoin_NativePowerQM66.mul a.c1 b.c1
  obtain ⟨q,hq,ohq⟩ := PV_RunJoin_NativePowerQM66.add a.c0 a.c1
  obtain ⟨q1,hq1,ohq1⟩ := PV_RunJoin_NativePowerQM66.add b.c0 b.c1
  obtain ⟨cross,hcross,ohcross⟩ := PV_RunJoin_NativePowerQM66.mul q q1
  obtain ⟨q2,hq2,ohq2⟩ := mul_u bd
  obtain ⟨q3,hq3,ohq3⟩ := PV_RunJoin_NativePowerQM66.add ac q2
  obtain ⟨q4,hq4,ohq4⟩ := PV_RunJoin_NativePowerQM66.sub cross ac
  obtain ⟨q5,hq5,ohq5⟩ := PV_RunJoin_NativePowerQM66.sub q4 bd
  refine ⟨⟨q3,q5⟩,?_,?_⟩
  · simp only [aspis_core.field.wide_exact.WideExact.mul,
    hac,hbd,hq,hq1,hcross,hq2,hq3,hq4,hq5,bind_tc_ok]
  · simp only [toS,AspisR1ProducerRelease47.field.wide_exact.WideExact.mul,ohac,ohbd,ohq,ohq1,ohcross,ohq2,ohq3,ohq4,ohq5,bind_tc_ok]
#print axioms mul
end R1Z.PV_RunJoin_NativePowerCarrier66
