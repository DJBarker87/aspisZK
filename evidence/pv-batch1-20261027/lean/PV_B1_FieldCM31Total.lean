import PV_B1_FieldM31Total
set_option autoImplicit false
namespace PV_B1_FieldCM31Total
open Aeneas Aeneas.Std Result PV_B1_254
abbrev C := aspis_core.field.CM31

theorem add (a b : C) : ∃ y, aspis_core.field.CM31.add a b=ok y := by
  obtain ⟨x,hx⟩ := PV_B1_FieldM31Total.add a.a b.a
  obtain ⟨y,hy⟩ := PV_B1_FieldM31Total.add a.b b.b
  exact ⟨⟨x,y⟩,by simp only [aspis_core.field.CM31.add,hx,hy,bind_tc_ok]⟩

theorem sub (a b : C) : ∃ y, aspis_core.field.CM31.sub a b=ok y := by
  obtain ⟨x,hx⟩ := PV_B1_FieldM31Total.sub a.a b.a
  obtain ⟨y,hy⟩ := PV_B1_FieldM31Total.sub a.b b.b
  exact ⟨⟨x,y⟩,by simp only [aspis_core.field.CM31.sub,hx,hy,bind_tc_ok]⟩

theorem mul (a b : C) : ∃ y, aspis_core.field.CM31.mul a b=ok y := by
  obtain ⟨m0,h0⟩ := PV_B1_FieldM31Total.mul a.a b.a
  obtain ⟨m1,h1⟩ := PV_B1_FieldM31Total.mul a.b b.b
  let prod := U64.wrapping_mul
    (U64.wrapping_add (core.convert.num.FromU64U32.from a.a) (core.convert.num.FromU64U32.from a.b))
    (U64.wrapping_add (core.convert.num.FromU64U32.from b.a) (core.convert.num.FromU64U32.from b.b))
  obtain ⟨m2,h2⟩ := PV_B1_FieldM31Total.reduce64 prod
  obtain ⟨m,hm⟩ := PV_B1_FieldM31Total.sub m0 m1
  obtain ⟨m3,h3⟩ := PV_B1_FieldM31Total.sub m2 m0
  obtain ⟨m4,h4⟩ := PV_B1_FieldM31Total.sub m3 m1
  exact ⟨⟨m,m4⟩,by simp only [aspis_core.field.CM31.mul,lift,bind_tc_ok,h0,h1,h2,hm,h3,h4]⟩

theorem mul_by_r (a : C) : ∃ y, aspis_core.field.mul_by_r a=ok y := by
  obtain ⟨m,hm⟩ := PV_B1_FieldM31Total.double a.a
  obtain ⟨m1,h1⟩ := PV_B1_FieldM31Total.sub m a.b
  obtain ⟨m2,h2⟩ := PV_B1_FieldM31Total.double a.b
  obtain ⟨m3,h3⟩ := PV_B1_FieldM31Total.add a.a m2
  exact ⟨⟨m1,m3⟩,by simp only [aspis_core.field.mul_by_r,hm,h1,h2,h3,bind_tc_ok]⟩
#print axioms add
#print axioms sub
#print axioms mul
#print axioms mul_by_r
end PV_B1_FieldCM31Total
