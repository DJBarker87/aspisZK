import R1Z.PV_RunJoin_CircleNeutralMul53
import R1Z.PV_RunJoin_CircleNeutralSub53
import R1Z.PV_RunJoin_CircleNeutralWide53
import R1Z.PV_RunJoin_CircleNeutralR23_53
import R1Z.PV_RunJoin_CircleNeutralMReduce53
import R1Z.PV_RunJoin_CircleNeutralWrappers53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralCMul53
open PV_RunJoin_CircleNeutralShape53 PV_RunJoin_CircleNeutralWide53

theorem complete (a b : U32 × U32) (ha : CC a) (hb : CC b) :
    ∃ y, PV_RunJoin_CircleRawTower52.field.CM31.mul a b = ok y ∧
      PV_RunJoin_CircleR72Raw52.field.CM31.mul a b = ok y ∧ CC y := by
  obtain ⟨m0,h0,h0',hc0⟩ := PV_RunJoin_CircleNeutralMul53.complete a.1 b.1 ha.1 hb.1
  obtain ⟨m1,h1,h1',hc1⟩ := PV_RunJoin_CircleNeutralMul53.complete a.2 b.2 ha.2 hb.2
  let prod := U64.wrapping_mul (sum a) (sum b)
  have hp : (sum a).val*(sum b).val < 18446744073709551616 := by
    have ha' := sum_bound a ha
    have hb' := sum_bound b hb
    have h := Nat.mul_lt_mul_of_lt_of_lt ha' hb'
    omega
  obtain ⟨m2,h2,h2',hc2⟩ := PV_RunJoin_CircleNeutralMReduce53.complete prod
  obtain ⟨y0,h3,h3',hc3⟩ := PV_RunJoin_CircleNeutralSub53.complete m0 m1 hc0 hc1
  obtain ⟨s,h4,h4',hc4⟩ := PV_RunJoin_CircleNeutralSub53.complete m2 m0 hc2 hc0
  obtain ⟨y1,h5,h5',hc5⟩ := PV_RunJoin_CircleNeutralSub53.complete s m1 hc4 hc1
  refine ⟨(y0,y1),?_,?_,hc3,hc5⟩
  · unfold PV_RunJoin_CircleRawTower52.field.CM31.mul
    simp only [h0,h1,lift,bind_tc_ok,from32,PV_RunJoin_CircleNeutralWrappers53.add64]
    change (do
      let z ← PV_RunJoin_CircleRawScalar52.field.M31.reduce_u64 prod
      let r ← PV_RunJoin_CircleRawScalar52.field.M31.sub m0 m1
      let t ← PV_RunJoin_CircleRawScalar52.field.M31.sub z m0
      let u ← PV_RunJoin_CircleRawScalar52.field.M31.sub t m1
      ok (r,u)) = _
    simp only [h2,h3,h4,h5,bind_tc_ok]
  · unfold PV_RunJoin_CircleR72Raw52.field.CM31.mul
    simp only [h0',h1',lift,bind_tc_ok,from32,sum_checked a ha,sum_checked b hb,
      PV_RunJoin_CircleNeutralR23_53.complete]
    rw [PV_RunJoin_CircleNeutralChecked64_53.mul _ _ hp]
    simp only [prod] at h2'
    simp only [bind_tc_ok,h2',h3',h4',h5']

#print axioms complete
end R1Z.PV_RunJoin_CircleNeutralCMul53
