import R1Z.PV_RunJoin_NeutralCAddValue54
import R1Z.PV_RunJoin_NeutralSubValue54
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_NeutralRValue54
open PV_RunJoin_NeutralValue54 PV_RunJoin_NeutralTowerValue54 PV_RunJoin_CircleNeutralShape53

theorem complete (a : C) (ha : CC a) :
    ∃ y, PV_RunJoin_CircleRawTower52.field.mul_by_r a=ok y ∧ CC y ∧ cv y=cr (cv a) := by
  obtain ⟨d0,h0,hc0,hv0⟩ := PV_RunJoin_NeutralAddValue54.complete a.1 a.1 ha.1 ha.1
  obtain ⟨y0,h1,hc1,hv1⟩ := PV_RunJoin_NeutralSubValue54.complete d0 a.2 hc0 ha.2
  obtain ⟨d1,h2,hc2,hv2⟩ := PV_RunJoin_NeutralAddValue54.complete a.2 a.2 ha.2 ha.2
  obtain ⟨y1,h3,hc3,hv3⟩ := PV_RunJoin_NeutralAddValue54.complete a.1 d1 ha.1 hc2
  refine ⟨(y0,y1),?_,⟨hc1,hc3⟩,?_⟩
  · unfold PV_RunJoin_CircleRawTower52.field.mul_by_r PV_RunJoin_CircleRawScalar52.field.M31.double
    rw [h0,bind_tc_ok,h1,bind_tc_ok,h2,bind_tc_ok,h3,bind_tc_ok]
  · apply Prod.ext
    · change scalar y0=2*scalar a.1-scalar a.2
      rw [hv1,hv0];ring
    · change scalar y1=scalar a.1+2*scalar a.2
      rw [hv3,hv2];ring
#print axioms complete
end R1Z.PV_RunJoin_NeutralRValue54
