import R1Z.PV_RunJoin_CircleNeutralInv53
import R1Z.PV_RunJoin_CircleNeutralMul53
import R1Z.PV_RunJoin_CircleNeutralAddCanon53
import R1Z.PV_RunJoin_CircleNeutralNeg53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralCInv53
open PV_RunJoin_CircleNeutralShape53 PV_RunJoin_CircleNeutralResult53

theorem complete (a : U32 × U32) (ha : CC a) :
    Aligned CC (PV_RunJoin_CircleRawTower52.field.CM31.inv a)
      (PV_RunJoin_CircleR72Raw52.field.CM31.inv a) := by
  obtain ⟨m0,h0,h0',hc0⟩ := PV_RunJoin_CircleNeutralMul53.complete a.1 a.1 ha.1 ha.1
  obtain ⟨m1,h1,h1',hc1⟩ := PV_RunJoin_CircleNeutralMul53.complete a.2 a.2 ha.2 ha.2
  obtain ⟨norm,h2,h2',hc2⟩ := PV_RunJoin_CircleNeutralAddCanon53.complete m0 m1 hc0 hc1
  unfold PV_RunJoin_CircleRawTower52.field.CM31.inv PV_RunJoin_CircleRawTower52.field.CM31.inv_with
    PV_RunJoin_CircleR72Raw52.field.CM31.inv PV_RunJoin_CircleR72Raw52.field.CM31.inv_with
  simp only [h0,h0',h1,h1',h2,h2',bind_tc_ok]
  apply PV_RunJoin_CircleNeutralResult53.bind (PV_RunJoin_CircleNeutralInv53.complete norm hc2)
  intro v hv
  obtain ⟨y0,h3,h3',hc3⟩ := PV_RunJoin_CircleNeutralMul53.complete a.1 v ha.1 hv
  obtain ⟨neg,h4,h4',hc4⟩ := PV_RunJoin_CircleNeutralNeg53.complete a.2 ha.2
  obtain ⟨y1,h5,h5',hc5⟩ := PV_RunJoin_CircleNeutralMul53.complete neg v hc4 hv
  apply returned CC _ _ (y0,y1)
  · simp only [h3,h4,h5,bind_tc_ok]
  · simp only [h3',h4',h5',bind_tc_ok]
  · exact ⟨hc3,hc5⟩

#print axioms complete
end R1Z.PV_RunJoin_CircleNeutralCInv53
