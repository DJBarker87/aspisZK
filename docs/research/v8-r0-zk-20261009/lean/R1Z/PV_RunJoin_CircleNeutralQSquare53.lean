import R1Z.PV_RunJoin_CircleNeutralCSquare53
import R1Z.PV_RunJoin_CircleNeutralRMul53
import R1Z.PV_RunJoin_CircleNeutralCAdd53
import R1Z.PV_RunJoin_CircleNeutralCMul53
import R1Z.PV_RunJoin_CircleNeutralCDouble53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralQSquare53
open PV_RunJoin_CircleNeutralShape53

theorem complete (a : (U32 × U32) × (U32 × U32)) (ha : QC a) :
    ∃ y, PV_RunJoin_CircleRawTower52.field.QM31.square a = ok y ∧
      PV_RunJoin_CircleR72Raw52.field.QM31.square a = ok y ∧ QC y := by
  obtain ⟨s0,h0,h0',hc0⟩ := PV_RunJoin_CircleNeutralCSquare53.complete a.1 ha.1
  obtain ⟨s1,h1,h1',hc1⟩ := PV_RunJoin_CircleNeutralCSquare53.complete a.2 ha.2
  obtain ⟨r,h2,h2',hc2⟩ := PV_RunJoin_CircleNeutralRMul53.complete s1 hc1
  obtain ⟨y0,h3,h3',hc3⟩ := PV_RunJoin_CircleNeutralCAdd53.complete s0 r hc0 hc2
  obtain ⟨m,h4,h4',hc4⟩ := PV_RunJoin_CircleNeutralCMul53.complete a.1 a.2 ha.1 ha.2
  obtain ⟨y1,h5,h5',hc5⟩ := PV_RunJoin_CircleNeutralCDouble53.complete m hc4
  refine ⟨(y0,y1),?_,?_,hc3,hc5⟩
  · unfold PV_RunJoin_CircleRawTower52.field.QM31.square
    simp only [h0,h1,h2,h3,h4,h5,bind_tc_ok]
  · unfold PV_RunJoin_CircleR72Raw52.field.QM31.square
    simp only [h0',h1',h2',h3',h4',h5',bind_tc_ok]

#print axioms complete
end R1Z.PV_RunJoin_CircleNeutralQSquare53
