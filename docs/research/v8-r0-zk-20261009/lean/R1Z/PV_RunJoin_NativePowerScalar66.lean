import R1Z.PV_RunJoin_NativeResidual63
import R1Z.PV_RunJoin_CircleNeutralScalar52
import AspisR1ProducerRelease47.Funs
import R1Z.PV_RunJoin_CircleNeutralWrappers53
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NativePowerScalar66
open Aeneas Aeneas.Std Result
open PV_B1_254

theorem subtract (x : U32) : aspis_core.field.ct.subtract_p x=
    ok (if x≥2147483647#u32 then U32.wrapping_sub x 2147483647#u32 else x) := by
  unfold aspis_core.field.ct.subtract_p aspis_core.field.P
  by_cases h : x≥2147483647#u32
  · simp only [h,decide_true,if_pos]
    rfl
  · simp only [h,decide_false,if_neg]
    change ok (U32.wrapping_sub x 0#u32)=ok x
    rw [PV_RunJoin_CircleNeutralScalar52.wrapping_sub_zero]

theorem reduce (x : U64) : aspis_core.field.reduce_u64 x=
    AspisR1ProducerRelease47.field.reduce_u64 x := by
  unfold aspis_core.field.reduce_u64 aspis_core.field.ct.reduce64 AspisR1ProducerRelease47.field.reduce_u64
  simp only [aspis_core.field.P,AspisR1ProducerRelease47.field.P,lift,bind_tc_ok,subtract,
    PV_RunJoin_CircleNeutralWrappers53.add32,PV_RunJoin_CircleNeutralWrappers53.sub32]
  split <;> simp_all only [if_pos,if_neg]

theorem add (x y : U32) : aspis_core.field.M31.add x y=
    AspisR1ProducerRelease47.field.M31.add x y := by
  unfold aspis_core.field.M31.add aspis_core.field.ct.add AspisR1ProducerRelease47.field.M31.add
  simp only [aspis_core.field.P,AspisR1ProducerRelease47.field.P,lift,bind_tc_ok,subtract,
    PV_RunJoin_CircleNeutralWrappers53.add32,PV_RunJoin_CircleNeutralWrappers53.sub32]
  split <;> simp_all only [if_pos,if_neg]

theorem sub (x y : U32) : aspis_core.field.M31.sub x y=
    AspisR1ProducerRelease47.field.M31.sub x y := by
  unfold aspis_core.field.M31.sub aspis_core.field.ct.sub AspisR1ProducerRelease47.field.M31.sub
  simp only [aspis_core.field.P,AspisR1ProducerRelease47.field.P,lift,bind_tc_ok,subtract,
    PV_RunJoin_CircleNeutralWrappers53.add32,PV_RunJoin_CircleNeutralWrappers53.sub32]
  split <;> simp_all only [if_pos,if_neg]

theorem mul (x y : U32) : aspis_core.field.M31.mul x y=
    AspisR1ProducerRelease47.field.M31.mul x y := by
  unfold aspis_core.field.M31.mul AspisR1ProducerRelease47.field.M31.mul
  simp only [lift,bind_tc_ok,reduce]
theorem mreduce (x : U64) : aspis_core.field.M31.reduce_u64 x=
    AspisR1ProducerRelease47.field.M31.reduce_u64 x := by
  unfold aspis_core.field.M31.reduce_u64 AspisR1ProducerRelease47.field.M31.reduce_u64
  rw [reduce]
theorem double (x : U32) : aspis_core.field.M31.double x=
    AspisR1ProducerRelease47.field.M31.double x := by
  unfold aspis_core.field.M31.double AspisR1ProducerRelease47.field.M31.double
  exact add x x
#print axioms mreduce
#print axioms double
#print axioms subtract
#print axioms reduce
#print axioms add
#print axioms sub
#print axioms mul
end R1Z.PV_RunJoin_NativePowerScalar66
