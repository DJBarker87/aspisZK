import R1Z.PV_RunJoin_CircleNeutralQInvEquation53
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RunJoin_CircleNeutralQInv53
open PV_RunJoin_CircleNeutralShape53 PV_RunJoin_CircleNeutralResult53

theorem complete (a : (U32 × U32) × (U32 × U32)) (ha : QC a) :
    Aligned PV_RunJoin_CircleNeutralQInvTail53.Valid
      (PV_RunJoin_CircleRawTower52.field.QM31.try_inv a)
      (PV_RunJoin_CircleR72Raw52.field.QM31.try_inv a) := by
  obtain ⟨z,hz,hz'⟩ := PV_RunJoin_CircleNeutralZeroResult53.qtotal a
  rw [PV_RunJoin_CircleNeutralQInvEquation53.owned,PV_RunJoin_CircleNeutralQInvEquation53.model]
  rw [hz,hz',bind_tc_ok,bind_tc_ok]
  cases z with
  | true => exact ⟨rfl,by intro x hx q hq;cases hx;cases hq⟩
  | false => exact PV_RunJoin_CircleNeutralQInvBody53.complete a ha
#print axioms complete
end R1Z.PV_RunJoin_CircleNeutralQInv53
