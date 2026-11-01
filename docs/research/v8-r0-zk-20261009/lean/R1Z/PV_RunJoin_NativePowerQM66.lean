import R1Z.PV_RunJoin_NativePowerCM66
import PV_B1_FieldQM31Total
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NativePowerQM66
open Aeneas Aeneas.Std Result PV_B1_254
abbrev Q := aspis_core.field.QM31
def toQ (x : Q) : AspisR1ProducerRelease47.field.QM31 :=
  ⟨PV_RunJoin_NativePowerCM66.toC x.c0,PV_RunJoin_NativePowerCM66.toC x.c1⟩
theorem add (a b : Q) : ∃ z,
    aspis_core.field.QM31.add a b=ok z ∧
    AspisR1ProducerRelease47.field.QM31.add (toQ a) (toQ b)=ok (toQ z) := by
  obtain ⟨x,hx,ohx⟩ := PV_RunJoin_NativePowerCM66.add a.c0 b.c0
  obtain ⟨y,hy,ohy⟩ := PV_RunJoin_NativePowerCM66.add a.c1 b.c1
  refine ⟨⟨x,y⟩,?_,?_⟩
  · simp only [aspis_core.field.QM31.add,hx,hy,bind_tc_ok]
  · simp only [toQ,AspisR1ProducerRelease47.field.QM31.add,ohx,ohy,bind_tc_ok]
#print axioms add
theorem sub (a b : Q) : ∃ z,
    aspis_core.field.QM31.sub a b=ok z ∧
    AspisR1ProducerRelease47.field.QM31.sub (toQ a) (toQ b)=ok (toQ z) := by
  obtain ⟨x,hx,ohx⟩ := PV_RunJoin_NativePowerCM66.sub a.c0 b.c0
  obtain ⟨y,hy,ohy⟩ := PV_RunJoin_NativePowerCM66.sub a.c1 b.c1
  refine ⟨⟨x,y⟩,?_,?_⟩
  · simp only [aspis_core.field.QM31.sub,hx,hy,bind_tc_ok]
  · simp only [toQ,AspisR1ProducerRelease47.field.QM31.sub,ohx,ohy,bind_tc_ok]
#print axioms sub
theorem mul (a b : Q) : ∃ z,
    aspis_core.field.QM31.mul a b=ok z ∧
    AspisR1ProducerRelease47.field.QM31.mul (toQ a) (toQ b)=ok (toQ z) := by
  obtain ⟨m0,h0,oh0⟩ := PV_RunJoin_NativePowerCM66.mul a.c0 b.c0
  obtain ⟨m1,h1,oh1⟩ := PV_RunJoin_NativePowerCM66.mul a.c1 b.c1
  obtain ⟨c,hc,ohc⟩ := PV_RunJoin_NativePowerCM66.add a.c0 a.c1
  obtain ⟨c1,hc1,ohc1⟩ := PV_RunJoin_NativePowerCM66.add b.c0 b.c1
  obtain ⟨m2,h2,oh2⟩ := PV_RunJoin_NativePowerCM66.mul c c1
  obtain ⟨c2,hc2,ohc2⟩ := PV_RunJoin_NativePowerCM66.mul_by_r m1
  obtain ⟨c3,hc3,ohc3⟩ := PV_RunJoin_NativePowerCM66.add m0 c2
  obtain ⟨c4,hc4,ohc4⟩ := PV_RunJoin_NativePowerCM66.sub m2 m0
  obtain ⟨c5,hc5,ohc5⟩ := PV_RunJoin_NativePowerCM66.sub c4 m1
  refine ⟨⟨c3,c5⟩,?_,?_⟩
  · simp only [aspis_core.field.QM31.mul,h0,h1,hc,hc1,h2,hc2,hc3,hc4,hc5,bind_tc_ok]
  · simp only [toQ,AspisR1ProducerRelease47.field.QM31.mul,oh0,oh1,ohc,ohc1,oh2,ohc2,ohc3,ohc4,ohc5,bind_tc_ok]
#print axioms mul
end R1Z.PV_RunJoin_NativePowerQM66
