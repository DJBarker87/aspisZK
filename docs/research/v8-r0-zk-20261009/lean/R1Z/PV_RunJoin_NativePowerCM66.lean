import R1Z.PV_RunJoin_NativePowerScalar66
import PV_B1_FieldCM31Total
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NativePowerCM66
open Aeneas Aeneas.Std Result PV_B1_254
abbrev C := aspis_core.field.CM31
def toC (x : C) : AspisR1ProducerRelease47.field.CM31 := ⟨x.a,x.b⟩
theorem add (a b : C) : ∃ z,
    aspis_core.field.CM31.add a b=ok z ∧
    AspisR1ProducerRelease47.field.CM31.add (toC a) (toC b)=ok (toC z) := by
  obtain ⟨x,hx⟩ := PV_B1_FieldM31Total.add a.a b.a
  obtain ⟨y,hy⟩ := PV_B1_FieldM31Total.add a.b b.b
  refine ⟨⟨x,y⟩,?_,?_⟩
  · simp only [aspis_core.field.CM31.add,hx,hy,bind_tc_ok]
  · simp only [toC,←PV_RunJoin_NativePowerScalar66.add,←PV_RunJoin_NativePowerScalar66.sub,
      ←PV_RunJoin_NativePowerScalar66.mul,←PV_RunJoin_NativePowerScalar66.mreduce,
      ←PV_RunJoin_NativePowerScalar66.double,AspisR1ProducerRelease47.field.CM31.add,hx,hy,bind_tc_ok]
#print axioms add
theorem sub (a b : C) : ∃ z,
    aspis_core.field.CM31.sub a b=ok z ∧
    AspisR1ProducerRelease47.field.CM31.sub (toC a) (toC b)=ok (toC z) := by
  obtain ⟨x,hx⟩ := PV_B1_FieldM31Total.sub a.a b.a
  obtain ⟨y,hy⟩ := PV_B1_FieldM31Total.sub a.b b.b
  refine ⟨⟨x,y⟩,?_,?_⟩
  · simp only [aspis_core.field.CM31.sub,hx,hy,bind_tc_ok]
  · simp only [toC,←PV_RunJoin_NativePowerScalar66.add,←PV_RunJoin_NativePowerScalar66.sub,
      ←PV_RunJoin_NativePowerScalar66.mul,←PV_RunJoin_NativePowerScalar66.mreduce,
      ←PV_RunJoin_NativePowerScalar66.double,AspisR1ProducerRelease47.field.CM31.sub,hx,hy,bind_tc_ok]
#print axioms sub
theorem mul (a b : C) : ∃ z,
    aspis_core.field.CM31.mul a b=ok z ∧
    AspisR1ProducerRelease47.field.CM31.mul (toC a) (toC b)=ok (toC z) := by
  obtain ⟨m0,h0⟩ := PV_B1_FieldM31Total.mul a.a b.a
  obtain ⟨m1,h1⟩ := PV_B1_FieldM31Total.mul a.b b.b
  let prod := U64.wrapping_mul
    (U64.wrapping_add (core.convert.num.FromU64U32.from a.a) (core.convert.num.FromU64U32.from a.b))
    (U64.wrapping_add (core.convert.num.FromU64U32.from b.a) (core.convert.num.FromU64U32.from b.b))
  obtain ⟨m2,h2⟩ := PV_B1_FieldM31Total.reduce64 prod
  dsimp only [prod] at h2
  obtain ⟨m,hm⟩ := PV_B1_FieldM31Total.sub m0 m1
  obtain ⟨m3,h3⟩ := PV_B1_FieldM31Total.sub m2 m0
  obtain ⟨m4,h4⟩ := PV_B1_FieldM31Total.sub m3 m1
  refine ⟨⟨m,m4⟩,?_,?_⟩
  · simp only [aspis_core.field.CM31.mul,lift,bind_tc_ok,h0,h1,h2,hm,h3,h4]
  · simp only [toC,←PV_RunJoin_NativePowerScalar66.add,←PV_RunJoin_NativePowerScalar66.sub,
      ←PV_RunJoin_NativePowerScalar66.mul,←PV_RunJoin_NativePowerScalar66.mreduce,
      ←PV_RunJoin_NativePowerScalar66.double,AspisR1ProducerRelease47.field.CM31.mul,lift,bind_tc_ok,h0,h1,h2,hm,h3,h4]
#print axioms mul
theorem mul_by_r (a : C) : ∃ z,
    aspis_core.field.mul_by_r a=ok z ∧
    AspisR1ProducerRelease47.field.mul_by_r (toC a)=ok (toC z) := by
  obtain ⟨m,hm⟩ := PV_B1_FieldM31Total.double a.a
  obtain ⟨m1,h1⟩ := PV_B1_FieldM31Total.sub m a.b
  obtain ⟨m2,h2⟩ := PV_B1_FieldM31Total.double a.b
  obtain ⟨m3,h3⟩ := PV_B1_FieldM31Total.add a.a m2
  refine ⟨⟨m1,m3⟩,?_,?_⟩
  · simp only [aspis_core.field.mul_by_r,hm,h1,h2,h3,bind_tc_ok]
  · simp only [toC,←PV_RunJoin_NativePowerScalar66.add,←PV_RunJoin_NativePowerScalar66.sub,
      ←PV_RunJoin_NativePowerScalar66.mul,←PV_RunJoin_NativePowerScalar66.mreduce,
      ←PV_RunJoin_NativePowerScalar66.double,AspisR1ProducerRelease47.field.mul_by_r,hm,h1,h2,h3,bind_tc_ok]
#print axioms mul_by_r
end R1Z.PV_RunJoin_NativePowerCM66
