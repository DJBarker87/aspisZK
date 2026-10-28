import R1Z.ProverRwP7CurrentCtBridge
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP7CurrentBaseBridge
open Aeneas Aeneas.Std Result
namespace S
abbrev reduce := ProverRwP7CurrentFieldSource.aspis_core.field.reduce_u64
abbrev mreduce := ProverRwP7CurrentFieldSource.aspis_core.field.M31.reduce_u64
abbrev mul := ProverRwP7CurrentFieldSource.aspis_core.field.M31.mul
abbrev add := ProverRwP7CurrentFieldSource.aspis_core.field.M31.add
abbrev sub := ProverRwP7CurrentFieldSource.aspis_core.field.M31.sub
abbrev double := ProverRwP7CurrentFieldSource.aspis_core.field.M31.double
end S

theorem reduce (x : U64) : S.reduce x = AspisR1ProducerRelease47.field.reduce_u64 x :=
  ProverRwP7CurrentCtBridge.reduce_source x

theorem mreduce (x : U64) : S.mreduce x = AspisR1ProducerRelease47.field.M31.reduce_u64 x := by
  simp only [S.mreduce,ProverRwP7CurrentFieldSource.aspis_core.field.M31.reduce_u64,
    reduce,AspisR1ProducerRelease47.field.M31.reduce_u64]

theorem mul (a b : U32) : S.mul a b = AspisR1ProducerRelease47.field.M31.mul a b := by
  simp only [S.mul,ProverRwP7CurrentFieldSource.aspis_core.field.M31.mul,reduce,
    AspisR1ProducerRelease47.field.M31.mul,lift,bind_tc_ok]

theorem add (a b : U32) : S.add a b = AspisR1ProducerRelease47.field.M31.add a b := by
  simp only [S.add,ProverRwP7CurrentFieldSource.aspis_core.field.M31.add,
    ProverRwP7CurrentCtBridge.add_source]
  cases AspisR1ProducerRelease47.field.M31.add a b <;> rfl

theorem sub (a b : U32) : S.sub a b = AspisR1ProducerRelease47.field.M31.sub a b := by
  simp only [S.sub,ProverRwP7CurrentFieldSource.aspis_core.field.M31.sub,
    ProverRwP7CurrentCtBridge.sub_source]
  cases AspisR1ProducerRelease47.field.M31.sub a b <;> rfl

theorem double (a : U32) : S.double a = AspisR1ProducerRelease47.field.M31.double a := by
  exact add a a
#print axioms reduce
#print axioms mreduce
#print axioms mul
#print axioms add
#print axioms sub
#print axioms double
end R1Z.ProverRwP7CurrentBaseBridge
