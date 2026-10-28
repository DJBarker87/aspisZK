import R1Z.PV_RunJoin_WeightScalar46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightComplex46
open Aeneas Aeneas.Std Result
abbrev C := PV_B2_251c1.aspis_core.field.CM31
abbrev MC := AspisR1ProducerRelease47.field.CM31
def toC (c : C) : MC := ⟨c.a,c.b⟩

theorem add (a b : C) :
    AspisR1ProducerRelease47.field.CM31.add (toC a) (toC b)=
      ok (toC (PV_B2_C_251FieldValue.aspis_core.field.CM31.add a b)) := by
  simp only [AspisR1ProducerRelease47.field.CM31.add,
    PV_B2_C_251FieldValue.aspis_core.field.CM31.add,toC,
    PV_RunJoin_WeightScalar46.add,bind_tc_ok]

theorem sub (a b : C) :
    AspisR1ProducerRelease47.field.CM31.sub (toC a) (toC b)=
      ok (toC (PV_B2_C_251FieldValue.aspis_core.field.CM31.sub a b)) := by
  simp only [AspisR1ProducerRelease47.field.CM31.sub,
    PV_B2_C_251FieldValue.aspis_core.field.CM31.sub,toC,
    PV_RunJoin_WeightScalar46.sub,bind_tc_ok]

theorem mul (a b : C) :
    AspisR1ProducerRelease47.field.CM31.mul (toC a) (toC b)=
      ok (toC (PV_B2_C_251FieldValue.aspis_core.field.CM31.mul a b)) := by
  simp only [AspisR1ProducerRelease47.field.CM31.mul,
    PV_B2_C_251FieldValue.aspis_core.field.CM31.mul,toC,
    PV_RunJoin_WeightScalar46.mul,PV_RunJoin_WeightScalar46.reduce_m31,
    PV_RunJoin_WeightScalar46.sub,lift,bind_tc_ok]

theorem r_mul (a : C) :
    AspisR1ProducerRelease47.field.mul_by_r (toC a)=
      ok (toC (PV_B2_C_251FieldValue.aspis_core.field.mul_by_r a)) := by
  simp only [AspisR1ProducerRelease47.field.mul_by_r,
    PV_B2_C_251FieldValue.aspis_core.field.mul_by_r,toC,
    PV_RunJoin_WeightScalar46.double,PV_RunJoin_WeightScalar46.add,
    PV_RunJoin_WeightScalar46.sub,bind_tc_ok]

#print axioms add
#print axioms sub
#print axioms mul
#print axioms r_mul
end R1Z.PV_RunJoin_WeightComplex46
