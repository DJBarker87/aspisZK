import NMT_345Validator
set_option autoImplicit false
noncomputable section
namespace NMT_R2_ValidatorPayment
open Aeneas Aeneas.Std
abbrev Statement := NFY_NBN_StatementResult.Statement

def value (s : Statement) :=
 match s with
 | .PrivateTransfer _ p => NFY_NBP_PaymentModel.transfer_encoded p
 | .Withdrawal _ p => NFY_NBP_PaymentModel.withdrawal_encoded p

theorem source (s : Statement) : NFY_NBN_StatementResult.payment s = .ok (value s) := by
 cases s with
 | PrivateTransfer c p => exact NFY_NBP_TransferEncode.result p
 | Withdrawal c p => exact NFY_NBP_WithdrawalEncode.result p
#print axioms source
end NMT_R2_ValidatorPayment
end
