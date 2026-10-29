import R1Z.PV_RunJoin_CircleNeutralAddCanon53
import R1Z.PV_RunJoin_CircleNeutralSub53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralRMul53
open PV_RunJoin_CircleNeutralShape53

theorem complete (a : U32 × U32) (ha : CC a) :
    ∃ y, PV_RunJoin_CircleRawTower52.field.mul_by_r a = ok y ∧
      PV_RunJoin_CircleR72Raw52.field.mul_by_r a = ok y ∧ CC y := by
  obtain ⟨d0,h0,h0',hc0⟩ := PV_RunJoin_CircleNeutralAddCanon53.complete a.1 a.1 ha.1 ha.1
  obtain ⟨y0,h1,h1',hc1⟩ := PV_RunJoin_CircleNeutralSub53.complete d0 a.2 hc0 ha.2
  obtain ⟨d1,h2,h2',hc2⟩ := PV_RunJoin_CircleNeutralAddCanon53.complete a.2 a.2 ha.2 ha.2
  obtain ⟨y1,h3,h3',hc3⟩ := PV_RunJoin_CircleNeutralAddCanon53.complete a.1 d1 ha.1 hc2
  refine ⟨(y0,y1),?_,?_,hc1,hc3⟩
  · unfold PV_RunJoin_CircleRawTower52.field.mul_by_r
    simp only [PV_RunJoin_CircleRawScalar52.field.M31.double,h0,h1,h2,h3,bind_tc_ok]
  · unfold PV_RunJoin_CircleR72Raw52.field.mul_by_r
    simp only [PV_RunJoin_CircleR72Raw52.field.M31.double,h0',h1',h2',h3',bind_tc_ok]

#print axioms complete
end R1Z.PV_RunJoin_CircleNeutralRMul53
