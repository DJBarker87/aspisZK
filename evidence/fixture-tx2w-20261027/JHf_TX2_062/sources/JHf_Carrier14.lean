import JHf_Carrier13
set_option autoImplicit false
namespace AspisR1.JHf_Carrier
open Aeneas Aeneas.Std Result
abbrev Payment := AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalPaymentV1
abbrev RawPayment := AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalPaymentV1

def toPayment : Payment → RawPayment
  | .PrivateTransfer p=>.PrivateTransfer (toPoolV1PrivateTransferPublicV1 p)
  | .Withdrawal p=>.Withdrawal (toPoolV1WithdrawalPublicV1 p)
def fromPayment : RawPayment → Payment
  | .PrivateTransfer p=>.PrivateTransfer (fromPoolV1PrivateTransferPublicV1 p)
  | .Withdrawal p=>.Withdrawal (fromPoolV1WithdrawalPublicV1 p)

theorem from_toPayment (p : Payment) : fromPayment (toPayment p)=p := by
  cases p <;> simp only [fromPayment,toPayment,from_toPoolV1PrivateTransferPublicV1,from_toPoolV1WithdrawalPublicV1]
#print axioms from_toPayment

abbrev Request := AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
abbrev RawRequest := AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
def toRequest (r : Request) : RawRequest :=
  ⟨r.verifier_profile,r.verifier_release,r.pool_program,toPayment r.«public»⟩
def fromRequest (r : RawRequest) : Request :=
  ⟨r.verifier_profile,r.verifier_release,r.pool_program,fromPayment r.«public»⟩
theorem from_toRequest (r : Request) : fromRequest (toRequest r)=r := by
  cases r
  simp only [fromRequest,toRequest,from_toPayment]
#print axioms from_toRequest
end AspisR1.JHf_Carrier
