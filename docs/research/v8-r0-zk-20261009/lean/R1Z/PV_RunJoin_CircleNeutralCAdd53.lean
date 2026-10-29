import R1Z.PV_RunJoin_CircleNeutralAddCanon53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralCAdd53
open PV_RunJoin_CircleNeutralShape53

theorem complete (a b : U32 × U32) (ha : CC a) (hb : CC b) :
    ∃ y, PV_RunJoin_CircleRawTower52.field.CM31.add a b = ok y ∧
      PV_RunJoin_CircleR72Raw52.field.CM31.add a b = ok y ∧ CC y := by
  obtain ⟨y0,h0,h0',hc0⟩ := PV_RunJoin_CircleNeutralAddCanon53.complete a.1 b.1 ha.1 hb.1
  obtain ⟨y1,h1,h1',hc1⟩ := PV_RunJoin_CircleNeutralAddCanon53.complete a.2 b.2 ha.2 hb.2
  refine ⟨(y0,y1),?_,?_,hc0,hc1⟩
  · unfold PV_RunJoin_CircleRawTower52.field.CM31.add
    simp only [h0,h1,bind_tc_ok]
  · unfold PV_RunJoin_CircleR72Raw52.field.CM31.add
    simp only [h0',h1',bind_tc_ok]

#print axioms complete
end R1Z.PV_RunJoin_CircleNeutralCAdd53
