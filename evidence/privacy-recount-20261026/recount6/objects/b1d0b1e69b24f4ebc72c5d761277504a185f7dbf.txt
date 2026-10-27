import PV_B1_FieldCM31Total
set_option autoImplicit false
namespace PV_B1_FieldQM31Total
open Aeneas Aeneas.Std Result PV_B1_254
abbrev Q := aspis_core.field.QM31

theorem add (a b : Q) : ∃ y, aspis_core.field.QM31.add a b=ok y := by
  obtain ⟨x,hx⟩ := PV_B1_FieldCM31Total.add a.c0 b.c0
  obtain ⟨y,hy⟩ := PV_B1_FieldCM31Total.add a.c1 b.c1
  exact ⟨⟨x,y⟩,by simp only [aspis_core.field.QM31.add,hx,hy,bind_tc_ok]⟩

theorem sub (a b : Q) : ∃ y, aspis_core.field.QM31.sub a b=ok y := by
  obtain ⟨x,hx⟩ := PV_B1_FieldCM31Total.sub a.c0 b.c0
  obtain ⟨y,hy⟩ := PV_B1_FieldCM31Total.sub a.c1 b.c1
  exact ⟨⟨x,y⟩,by simp only [aspis_core.field.QM31.sub,hx,hy,bind_tc_ok]⟩

theorem mul (a b : Q) : ∃ y, aspis_core.field.QM31.mul a b=ok y := by
  obtain ⟨m0,h0⟩ := PV_B1_FieldCM31Total.mul a.c0 b.c0
  obtain ⟨m1,h1⟩ := PV_B1_FieldCM31Total.mul a.c1 b.c1
  obtain ⟨c,hc⟩ := PV_B1_FieldCM31Total.add a.c0 a.c1
  obtain ⟨c1,hc1⟩ := PV_B1_FieldCM31Total.add b.c0 b.c1
  obtain ⟨m2,h2⟩ := PV_B1_FieldCM31Total.mul c c1
  obtain ⟨c2,hc2⟩ := PV_B1_FieldCM31Total.mul_by_r m1
  obtain ⟨c3,hc3⟩ := PV_B1_FieldCM31Total.add m0 c2
  obtain ⟨c4,hc4⟩ := PV_B1_FieldCM31Total.sub m2 m0
  obtain ⟨c5,hc5⟩ := PV_B1_FieldCM31Total.sub c4 m1
  exact ⟨⟨c3,c5⟩,by simp only [aspis_core.field.QM31.mul,h0,h1,hc,hc1,h2,hc2,hc3,hc4,hc5,bind_tc_ok]⟩
#print axioms add
#print axioms sub
#print axioms mul
end PV_B1_FieldQM31Total
