import NED_ValidatorStatus
import NED_RawWordArrayEq
set_option autoImplicit false
namespace NED_StatementCarrierFields
open NED_ReconstructCarriers NED_PaymentCohorts NED_LateCarriers

theorem transfer (c : NED_ReconstructCarriers.Common) (p : T) :
    toRaw (.PrivateTransfer c p) =
    .PrivateTransfer (NED_ReconstructCarriers.toRawCommon c) (toRawTransfer p) := by rfl

theorem withdrawal (c : NED_ReconstructCarriers.Common) (p : W) :
    toRaw (.Withdrawal c p) =
    .Withdrawal (NED_ReconstructCarriers.toRawCommon c) (toRawWithdrawal p) := by rfl

theorem master (c : NED_ReconstructCarriers.Common) :
    (NED_ReconstructCarriers.toRawCommon c).master_account = c.master_account := by rfl
theorem checkpoint (c : NED_ReconstructCarriers.Common) :
    (NED_ReconstructCarriers.toRawCommon c).checkpoint_account = c.checkpoint_account := by rfl
theorem selected_lane (c : NED_ReconstructCarriers.Common) :
    (NED_ReconstructCarriers.toRawCommon c).selected_lane_account = c.selected_lane_account := by rfl
theorem lane (c : NED_ReconstructCarriers.Common) :
    (NED_ReconstructCarriers.toRawCommon c).output_lane = c.output_lane := by rfl
theorem sequence (c : NED_ReconstructCarriers.Common) :
    (NED_ReconstructCarriers.toRawCommon c).checkpoint_sequence = c.checkpoint_sequence := by rfl
theorem pool (s : TSnapshot) : (toRawSnapshot s).pool = s.pool := by rfl
theorem deployment (s : TSnapshot) : (toRawSnapshot s).deployment_domain = s.deployment_domain := by rfl

#print axioms transfer
#print axioms withdrawal
#print axioms master
#print axioms checkpoint
#print axioms selected_lane
#print axioms lane
#print axioms sequence
#print axioms pool
#print axioms deployment
end NED_StatementCarrierFields
