import R1Z.PV_RunJoin_CircleNeutralQInvEquation53
import R1Z.PV_RunJoin_CircleNeutralAlignedTransport53
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RunJoin_CircleNeutralQInv53
open PV_RunJoin_CircleNeutralShape53 PV_RunJoin_CircleNeutralResult53

theorem complete (a : (U32 × U32) × (U32 × U32)) (ha : QC a) :
    Aligned PV_RunJoin_CircleNeutralQInvTail53.Valid
      (PV_RunJoin_CircleRawTower52.field.QM31.try_inv a)
      (PV_RunJoin_CircleR72Raw52.field.QM31.try_inv a) := by
  obtain ⟨z,hz,hz'⟩ := PV_RunJoin_CircleNeutralZeroResult53.qtotal a
  apply PV_RunJoin_CircleNeutralAlignedTransport53.transport
    (PV_RunJoin_CircleNeutralQInvEquation53.owned a)
    (PV_RunJoin_CircleNeutralQInvEquation53.model a)
  have hzero : Aligned (fun _ : Bool => True)
      (PV_RunJoin_CircleRawTower52.field.QM31.is_zero a)
      (PV_RunJoin_CircleR72Raw52.field.QM31.is_zero a) :=
    returned _ _ _ z hz hz' True.intro
  apply PV_RunJoin_CircleNeutralResult53.bind hzero
  intro b _
  cases b with
  | true =>
    apply returned _ _ _ none rfl rfl
    intro q hq
    cases hq
  | false => exact PV_RunJoin_CircleNeutralQInvBody53.complete a ha
#print axioms complete
end R1Z.PV_RunJoin_CircleNeutralQInv53
