import R1Z.PV_RunJoin_WeightCarrier46
import R1Z.PV_B2_D_ScalarOperations
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightScalar46
open Aeneas Aeneas.Std Result

theorem add (a b : U32) : AspisR1ProducerRelease47.field.M31.add a b=ok (PV_B2_C_251FieldValue.aspis_core.field.M31.add a b) := by
  simp only [AspisR1ProducerRelease47.field.M31.add,PV_B2_C_251FieldValue.aspis_core.field.M31.add,PV_B2_C_251FieldValue.aspis_core.field.ct.add,PV_B2_D_ScalarOperations.subtract_shape,
    lift,bind_tc_ok]
  change (if U32.wrapping_add a b ≥ 2147483647#u32 then _ else _)=_
  split <;> rfl

theorem sub (a b : U32) : AspisR1ProducerRelease47.field.M31.sub a b=ok (PV_B2_C_251FieldValue.aspis_core.field.M31.sub a b) := by
  simp only [AspisR1ProducerRelease47.field.M31.sub,PV_B2_C_251FieldValue.aspis_core.field.M31.sub,PV_B2_C_251FieldValue.aspis_core.field.ct.sub,PV_B2_D_ScalarOperations.subtract_shape,
    lift,bind_tc_ok]
  change (if U32.wrapping_sub (U32.wrapping_add a 2147483647#u32) b ≥ 2147483647#u32 then _ else _)=_
  split <;> rfl

theorem reduce (x : U64) : AspisR1ProducerRelease47.field.reduce_u64 x=ok (PV_B2_C_251FieldValue.aspis_core.field.reduce_u64 x) := by
  simp only [AspisR1ProducerRelease47.field.reduce_u64,PV_B2_C_251FieldValue.aspis_core.field.reduce_u64,PV_B2_C_251FieldValue.aspis_core.field.ct.reduce64,
    PV_B2_D_ScalarOperations.subtract_shape,lift,bind_tc_ok]
  split <;> rfl

theorem mul (a b : U32) : AspisR1ProducerRelease47.field.M31.mul a b=ok (PV_B2_C_251FieldValue.aspis_core.field.M31.mul a b) := by
  simp only [AspisR1ProducerRelease47.field.M31.mul,PV_B2_C_251FieldValue.aspis_core.field.M31.mul,reduce,lift,bind_tc_ok]

theorem reduce_m31 (x : U64) : AspisR1ProducerRelease47.field.M31.reduce_u64 x=ok (PV_B2_C_251FieldValue.aspis_core.field.M31.reduce_u64 x) := by
  simp only [AspisR1ProducerRelease47.field.M31.reduce_u64,PV_B2_C_251FieldValue.aspis_core.field.M31.reduce_u64,reduce,bind_tc_ok]

theorem double (a : U32) : AspisR1ProducerRelease47.field.M31.double a=ok (PV_B2_C_251FieldValue.aspis_core.field.M31.double a) := add a a

#print axioms add
#print axioms sub
#print axioms reduce
#print axioms mul
#print axioms reduce_m31
#print axioms double
end R1Z.PV_RunJoin_WeightScalar46
