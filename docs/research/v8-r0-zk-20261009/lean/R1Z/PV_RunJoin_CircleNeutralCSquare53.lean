import R1Z.PV_RunJoin_CircleNeutralMul53
import R1Z.PV_RunJoin_CircleNeutralAddCanon53
import R1Z.PV_RunJoin_CircleNeutralWideMix53
import R1Z.PV_RunJoin_CircleNeutralR23_53
import R1Z.PV_RunJoin_CircleNeutralMReduce53
import R1Z.PV_RunJoin_CircleNeutralWrappers53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralCSquare53
open PV_RunJoin_CircleNeutralShape53 PV_RunJoin_CircleNeutralWide53 PV_RunJoin_CircleNeutralWideMix53

theorem complete (a : U32 × U32) (ha : CC a) :
    ∃ y, PV_RunJoin_CircleRawTower52.field.CM31.square a = ok y ∧
      PV_RunJoin_CircleR72Raw52.field.CM31.square a = ok y ∧ CC y := by
  let prod := U64.wrapping_mul (sum a) (mix a)
  have hp := product_bound (sum a) (mix a) (sum_bound a ha) (mix_bound a ha)
  obtain ⟨y0,h0,h0',hc0⟩ := PV_RunJoin_CircleNeutralMReduce53.complete prod
  obtain ⟨m,h1,h1',hc1⟩ := PV_RunJoin_CircleNeutralMul53.complete a.1 a.2 ha.1 ha.2
  obtain ⟨y1,h2,h2',hc2⟩ := PV_RunJoin_CircleNeutralAddCanon53.complete m m hc1 hc1
  refine ⟨(y0,y1),?_,?_,hc0,hc2⟩
  · unfold PV_RunJoin_CircleRawTower52.field.CM31.square
    simp only [lift,bind_tc_ok,from32,PV_RunJoin_CircleRawScalar52.field.P,
      PV_RunJoin_CircleNeutralWrappers53.add64,PV_RunJoin_CircleNeutralWrappers53.sub64]
    change (do
      let z ← PV_RunJoin_CircleRawScalar52.field.M31.reduce_u64 prod
      let t ← PV_RunJoin_CircleRawScalar52.field.M31.mul a.1 a.2
      let u ← PV_RunJoin_CircleRawScalar52.field.M31.double t
      ok (z,u)) = _
    simp only [h0,h1,PV_RunJoin_CircleRawScalar52.field.M31.double,h2,bind_tc_ok]
  · unfold PV_RunJoin_CircleR72Raw52.field.CM31.square
    simp only [lift,bind_tc_ok,from32,PV_RunJoin_CircleR72Raw52.field.P,
      sum_checked a ha,pad_checked a ha,mix_sub a ha,
      PV_RunJoin_CircleNeutralR23_53.complete]
    rw [PV_RunJoin_CircleNeutralChecked64_53.mul _ _ hp]
    simp only [h0',h1',PV_RunJoin_CircleR72Raw52.field.M31.double,h2',bind_tc_ok]

#print axioms complete
end R1Z.PV_RunJoin_CircleNeutralCSquare53
