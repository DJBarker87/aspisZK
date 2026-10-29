import NED_PaymentCohorts
set_option autoImplicit false
noncomputable section
namespace NED_RawCarrierInverses
open NED_ReconstructCarriers NED_PaymentCohorts

def fromRawTransfer (p : RT) : T := AspisS6CurrentAdapterCarrier.toPoolV1PrivateTransferPublicV1
  (AspisR1.JHf_Carrier.fromPoolV1PrivateTransferPublicV1 p)
def fromRawWithdrawal (p : RW) : W := AspisS6CurrentAdapterCarrier.toPoolV1WithdrawalPublicV1
  (AspisR1.JHf_Carrier.fromPoolV1WithdrawalPublicV1 p)

theorem common (p : RawCommon) : NED_ReconstructCarriers.toRawCommon (fromRawCommon p) = p := by
  cases p <;> rfl

theorem transfer (p : RT) : toRawTransfer (fromRawTransfer p) = p := by
  cases p <;> rfl

theorem withdrawal (p : RW) : toRawWithdrawal (fromRawWithdrawal p) = p := by
  cases p <;> rfl

theorem statement (p : Raw) : toRaw (fromRaw p) = p := by
  cases p <;> rfl

#print axioms common
#print axioms transfer
#print axioms withdrawal
#print axioms statement
end NED_RawCarrierInverses
