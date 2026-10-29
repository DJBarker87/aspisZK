import R1Z.PV_RunJoin_CircleNeutralCInv53
import R1Z.PV_RunJoin_CircleNeutralCSquare53
import R1Z.PV_RunJoin_CircleNeutralRMul53
import R1Z.PV_RunJoin_CircleNeutralCSub53
import R1Z.PV_RunJoin_CircleNeutralCMul53
import R1Z.PV_RunJoin_CircleNeutralCNeg53
import R1Z.PV_RunJoin_CircleNeutralZeroResult53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralQInv53
open PV_RunJoin_CircleNeutralShape53 PV_RunJoin_CircleNeutralResult53

theorem complete (a : (U32 × U32) × (U32 × U32)) (ha : QC a) :
    Aligned (fun x => ∀ q, x=some q → QC q)
      (PV_RunJoin_CircleRawTower52.field.QM31.try_inv a)
      (PV_RunJoin_CircleR72Raw52.field.QM31.try_inv a) := by
  obtain ⟨z,hz,hz'⟩ := PV_RunJoin_CircleNeutralZeroResult53.qtotal a
  unfold PV_RunJoin_CircleRawTower52.field.QM31.try_inv PV_RunJoin_CircleR72Raw52.field.QM31.try_inv
  simp only [hz,hz',bind_tc_ok]
  cases z with
  | true => exact ⟨rfl,by intro x hx q hq;cases hx;cases hq⟩
  | false =>
    simp only [Bool.false_eq_true,if_false]
    obtain ⟨s0,h0,h0',hc0⟩ := PV_RunJoin_CircleNeutralCSquare53.complete a.1 ha.1
    obtain ⟨s1,h1,h1',hc1⟩ := PV_RunJoin_CircleNeutralCSquare53.complete a.2 ha.2
    obtain ⟨r,h2,h2',hc2⟩ := PV_RunJoin_CircleNeutralRMul53.complete s1 hc1
    obtain ⟨norm,h3,h3',hc3⟩ := PV_RunJoin_CircleNeutralCSub53.complete s0 r hc0 hc2
    simp only [h0,h0',h1,h1',h2,h2',h3,h3',bind_tc_ok]
    apply PV_RunJoin_CircleNeutralResult53.bind (PV_RunJoin_CircleNeutralCInv53.complete norm hc3)
    intro v hv
    obtain ⟨y0,h4,h4',hc4⟩ := PV_RunJoin_CircleNeutralCMul53.complete a.1 v ha.1 hv
    obtain ⟨neg,h5,h5',hc5⟩ := PV_RunJoin_CircleNeutralCNeg53.complete a.2 ha.2
    obtain ⟨y1,h6,h6',hc6⟩ := PV_RunJoin_CircleNeutralCMul53.complete neg v hc5 hv
    apply returned _ _ _ (some (y0,y1))
    · simp only [h4,h5,h6,bind_tc_ok]
    · simp only [h4',h5',h6',bind_tc_ok]
    · intro q hq
      cases hq
      exact ⟨hc4,hc6⟩

#print axioms complete
end R1Z.PV_RunJoin_CircleNeutralQInv53
