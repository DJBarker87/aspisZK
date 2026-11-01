import R1Z.PV_RunJoin_NativeResidual63
import R1Z.PV_RunJoin_CircleNeutralScalar52
import AspisR1ProducerRelease47.Funs
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NativePowerScalar66
open Aeneas Aeneas.Std Result
open PV_B1_254

theorem subtract (x : U32) : aspis_core.field.ct.subtract_p x=
    ok (if x≥2147483647#u32 then U32.wrapping_sub x 2147483647#u32 else x) := by
  simpa only [aspis_core.field.ct.subtract_p,aspis_core.field.P,
    PV_RunJoin_CircleRawScalar52.field.ct.subtract_p,PV_RunJoin_CircleRawScalar52.field.P]
    using PV_RunJoin_CircleNeutralScalar52.subtract_shape x

theorem reduce (x : U64) : aspis_core.field.reduce_u64 x=
    AspisR1ProducerRelease47.field.reduce_u64 x := by
  unfold aspis_core.field.reduce_u64 aspis_core.field.ct.reduce64 AspisR1ProducerRelease47.field.reduce_u64
  simp only [aspis_core.field.P,AspisR1ProducerRelease47.field.P,lift,bind_tc_ok,subtract]
  split <;> rfl

theorem add (x y : U32) : aspis_core.field.M31.add x y=
    AspisR1ProducerRelease47.field.M31.add x y := by
  unfold aspis_core.field.M31.add aspis_core.field.ct.add AspisR1ProducerRelease47.field.M31.add
  simp only [aspis_core.field.P,AspisR1ProducerRelease47.field.P,lift,bind_tc_ok,subtract]
  split <;> rfl

theorem sub (x y : U32) : aspis_core.field.M31.sub x y=
    AspisR1ProducerRelease47.field.M31.sub x y := by
  unfold aspis_core.field.M31.sub aspis_core.field.ct.sub AspisR1ProducerRelease47.field.M31.sub
  simp only [aspis_core.field.P,AspisR1ProducerRelease47.field.P,lift,bind_tc_ok,subtract]
  split <;> rfl

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
