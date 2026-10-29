import R1Z.PV_RunJoin_CircleNeutralNeg53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralCNeg53
open PV_RunJoin_CircleNeutralShape53

theorem complete (a : U32 × U32) (ha : CC a) :
    ∃ y, PV_RunJoin_CircleRawTower52.field.CM31.neg a = ok y ∧
      PV_RunJoin_CircleR72Raw52.field.CM31.neg a = ok y ∧ CC y := by
  obtain ⟨y0,h0,h0',hc0⟩ := PV_RunJoin_CircleNeutralNeg53.complete a.1 ha.1
  obtain ⟨y1,h1,h1',hc1⟩ := PV_RunJoin_CircleNeutralNeg53.complete a.2 ha.2
  refine ⟨(y0,y1),?_,?_,hc0,hc1⟩
  · unfold PV_RunJoin_CircleRawTower52.field.CM31.neg
    simp only [h0,h1,bind_tc_ok]
  · unfold PV_RunJoin_CircleR72Raw52.field.CM31.neg
    simp only [h0',h1',bind_tc_ok]

#print axioms complete
end R1Z.PV_RunJoin_CircleNeutralCNeg53
