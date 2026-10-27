import PV_B1_FieldQM31Total
set_option autoImplicit false
namespace PV_B1_FieldWideTotal
open Aeneas Aeneas.Std Result PV_B1_254
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev Q := aspis_core.field.QM31

theorem mul_u (a : Q) : ∃ y, aspis_core.field.wide_exact.mul_u a=ok y := by
  obtain ⟨c,hc⟩ := PV_B1_FieldCM31Total.mul_by_r a.c1
  exact ⟨⟨c,a.c0⟩,by simp only [aspis_core.field.wide_exact.mul_u,hc,bind_tc_ok]⟩

theorem mul (a b : W) : ∃ y, aspis_core.field.wide_exact.WideExact.mul a b=ok y := by
  obtain ⟨ac,hac⟩ := PV_B1_FieldQM31Total.mul a.c0 b.c0
  obtain ⟨bd,hbd⟩ := PV_B1_FieldQM31Total.mul a.c1 b.c1
  obtain ⟨q,hq⟩ := PV_B1_FieldQM31Total.add a.c0 a.c1
  obtain ⟨q1,hq1⟩ := PV_B1_FieldQM31Total.add b.c0 b.c1
  obtain ⟨cross,hcross⟩ := PV_B1_FieldQM31Total.mul q q1
  obtain ⟨q2,hq2⟩ := mul_u bd
  obtain ⟨q3,hq3⟩ := PV_B1_FieldQM31Total.add ac q2
  obtain ⟨q4,hq4⟩ := PV_B1_FieldQM31Total.sub cross ac
  obtain ⟨q5,hq5⟩ := PV_B1_FieldQM31Total.sub q4 bd
  exact ⟨⟨q3,q5⟩,by simp only [aspis_core.field.wide_exact.WideExact.mul,
    hac,hbd,hq,hq1,hcross,hq2,hq3,hq4,hq5,bind_tc_ok]⟩
#print axioms mul_u
#print axioms mul
end PV_B1_FieldWideTotal
