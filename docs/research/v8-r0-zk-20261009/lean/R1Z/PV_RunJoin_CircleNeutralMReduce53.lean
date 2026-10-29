import R1Z.PV_RunJoin_CircleNeutralReduceCompare53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralMReduce53
theorem complete (x : U64) : ∃ y,
    PV_RunJoin_CircleRawScalar52.field.M31.reduce_u64 x = ok y ∧
    PV_RunJoin_CircleR72Raw52.field.M31.reduce_u64 x = ok y ∧
    PV_RunJoin_CircleNeutralShape53.Canon y := by
  obtain ⟨y,hy,hy',hc⟩ := PV_RunJoin_CircleNeutralReduceCompare53.total x
  refine ⟨y,?_,?_,hc⟩
  · unfold PV_RunJoin_CircleRawScalar52.field.M31.reduce_u64 PV_RunJoin_CircleRawScalar52.field.reduce_u64
    simp only [hy,bind_tc_ok]
  · unfold PV_RunJoin_CircleR72Raw52.field.M31.reduce_u64
    simp only [hy',bind_tc_ok]

#print axioms complete
end R1Z.PV_RunJoin_CircleNeutralMReduce53
