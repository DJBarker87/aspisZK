import R1Z.PV_RunJoin_WeightQuartic46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightWide46
open Aeneas Aeneas.Std Result PV_RunJoin_WeightCarrier46
open PV_RunJoin_WeightMap46 (mapResult)
abbrev E := PV_B2_251c1.aspis_core.field.wide_exact.WideExact
abbrev ME := AspisR1ProducerRelease47.field.wide_exact.WideExact
def toWide (x : E) : ME := ⟨toQ x.c0,toQ x.c1⟩

theorem mul_u_value (x : Q) :
    AspisR1ProducerRelease47.field.wide_exact.mul_u (toQ x)=
      ok (toQ (PV_B2_C_251WideValue.aspis_core.field.wide_exact.mul_u x)) := by
  change AspisR1ProducerRelease47.field.wide_exact.mul_u
    ⟨PV_RunJoin_WeightComplex46.toC x.c0,PV_RunJoin_WeightComplex46.toC x.c1⟩=_
  simp only [AspisR1ProducerRelease47.field.wide_exact.mul_u,
    PV_B2_C_251WideValue.aspis_core.field.wide_exact.mul_u,
    PV_RunJoin_WeightComplex46.r_mul,bind_tc_ok] <;> rfl
#print axioms mul_u_value

theorem add_value (x y : E) :
    AspisR1ProducerRelease47.field.wide_exact.WideExact.add (toWide x) (toWide y)=
      ok (toWide (PV_B2_C_251WideValue.aspis_core.field.wide_exact.WideExact.add x y)) := by
  simp only [AspisR1ProducerRelease47.field.wide_exact.WideExact.add,
    PV_B2_C_251WideValue.aspis_core.field.wide_exact.WideExact.add,toWide,
    PV_RunJoin_WeightQuartic46.add_value,bind_tc_ok] <;> rfl

theorem add (x y : E) :
    AspisR1ProducerRelease47.field.wide_exact.WideExact.add (toWide x) (toWide y)=
      mapResult toWide (PV_B2_251c1.aspis_core.field.wide_exact.WideExact.add x y) := by
  rw [PV_B2_C_251WideTotal.WideExact_add]
  exact add_value x y
#print axioms add_value
#print axioms add

theorem mul_value (x y : E) :
    AspisR1ProducerRelease47.field.wide_exact.WideExact.mul (toWide x) (toWide y)=
      ok (toWide (PV_B2_C_251WideValue.aspis_core.field.wide_exact.WideExact.mul x y)) := by
  simp only [AspisR1ProducerRelease47.field.wide_exact.WideExact.mul,
    PV_B2_C_251WideValue.aspis_core.field.wide_exact.WideExact.mul,toWide,
    PV_RunJoin_WeightQuartic46.add_value,PV_RunJoin_WeightQuartic46.mul_value,PV_RunJoin_WeightQuartic46.sub_value,mul_u_value,bind_tc_ok] <;> rfl

theorem mul (x y : E) :
    AspisR1ProducerRelease47.field.wide_exact.WideExact.mul (toWide x) (toWide y)=
      mapResult toWide (PV_B2_251c1.aspis_core.field.wide_exact.WideExact.mul x y) := by
  rw [PV_B2_C_251WideTotal.WideExact_mul]
  exact mul_value x y
#print axioms mul_value
#print axioms mul
end R1Z.PV_RunJoin_WeightWide46
