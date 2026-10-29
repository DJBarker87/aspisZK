import R1Z.PV_RunJoin_NeutralCMulValue54
import R1Z.PV_RunJoin_NeutralCAddValue54
import R1Z.PV_RunJoin_NeutralCSubValue54
import R1Z.PV_RunJoin_NeutralRValue54
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_NeutralQMulValue54
open PV_RunJoin_NeutralTowerValue54 PV_RunJoin_CircleNeutralShape53

theorem complete (a b : Q) (ha : QC a) (hb : QC b) :
    ∃ y, PV_RunJoin_CircleRawTower52.field.QM31.mul a b=ok y ∧ QC y ∧ qv y=qm (qv a) (qv b) := by
  obtain ⟨m0,h0,hc0,hv0⟩ := PV_RunJoin_NeutralCMulValue54.complete a.1 b.1 ha.1 hb.1
  obtain ⟨m1,h1,hc1,hv1⟩ := PV_RunJoin_NeutralCMulValue54.complete a.2 b.2 ha.2 hb.2
  obtain ⟨sa,h2,hc2,hv2⟩ := PV_RunJoin_NeutralCAddValue54.complete a.1 a.2 ha.1 ha.2
  obtain ⟨sb,h3,hc3,hv3⟩ := PV_RunJoin_NeutralCAddValue54.complete b.1 b.2 hb.1 hb.2
  obtain ⟨m2,h4,hc4,hv4⟩ := PV_RunJoin_NeutralCMulValue54.complete sa sb hc2 hc3
  obtain ⟨r,h5,hc5,hv5⟩ := PV_RunJoin_NeutralRValue54.complete m1 hc1
  obtain ⟨lo,h6,hc6,hv6⟩ := PV_RunJoin_NeutralCAddValue54.complete m0 r hc0 hc5
  obtain ⟨t,h7,hc7,hv7⟩ := PV_RunJoin_NeutralCSubValue54.complete m2 m0 hc4 hc0
  obtain ⟨hi,h8,hc8,hv8⟩ := PV_RunJoin_NeutralCSubValue54.complete t m1 hc7 hc1
  refine ⟨(lo,hi),?_,⟨hc6,hc8⟩,?_⟩
  · unfold PV_RunJoin_CircleRawTower52.field.QM31.mul
    rw [h0,bind_tc_ok,h1,bind_tc_ok,h2,bind_tc_ok,h3,bind_tc_ok,h4,bind_tc_ok,
      h5,bind_tc_ok,h6,bind_tc_ok,h7,bind_tc_ok,h8,bind_tc_ok]
  · change (cv lo,cv hi)=_
    rw [hv6,hv8,hv7,hv5,hv4,hv3,hv2,hv1,hv0]
    rfl
#print axioms complete
end R1Z.PV_RunJoin_NeutralQMulValue54
