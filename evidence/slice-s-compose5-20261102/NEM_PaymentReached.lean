import NEE_ReachedRootModel
import NED_CodecComposition
set_option autoImplicit false
noncomputable section
namespace NEM_PaymentReached
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NBN_StatementResult

def pay (s : Statement) :=
  NBN_ValidatorSummary.paymentWith
    pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1
    pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1 s

/-- Exact emitted payment child selected by this statement, including every
rejection and all returned bytes. Native certificates remain separate. -/
theorem payment_instance (s : Statement) : pay s = NED_ValidatorTrace.payment s := by
  cases s with
  | PrivateTransfer c p =>
    exact (NED_CodecComposition.transfer_law p).symm
  | Withdrawal c p =>
    exact (NED_CodecComposition.withdrawal_law p).symm

/-- The first reached-child law is supplied on the SAME argument; no payment
PacketDomain, accepted-result, or independent execution premise remains. -/
theorem payment_reached (lane : NEE_ValidatorMutation.Lane)
    (late : NEE_ValidatorMutation.Late) (s a : Statement)
    (_reached : NED_ValidatorTrace.Call.payment a ∈
      (NEE_ValidatorOracle.run pay lane late s).2) :
    pay a = NED_ValidatorTrace.payment a := payment_instance a

#print axioms payment_instance
#print axioms payment_reached
end NEM_PaymentReached
