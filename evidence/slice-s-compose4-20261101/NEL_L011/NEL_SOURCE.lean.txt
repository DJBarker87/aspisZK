import NED_PaymentCohorts
set_option autoImplicit false
noncomputable section
namespace NEL_PaymentFieldCarriers
open NED_PaymentCohorts

theorem transfer_fields (p : T) :
    (toRawTransfer p).recipient_commitment = p.recipient_commitment ∧
      (toRawTransfer p).change_commitment = p.change_commitment := by constructor <;> rfl

theorem withdrawal_fields (p : W) :
    (toRawWithdrawal p).change_commitment = p.change_commitment ∧
      (toRawWithdrawal p).amount = p.amount ∧
      (toRawWithdrawal p).destination_token_account = p.destination_token_account := by
  exact ⟨rfl,rfl,rfl⟩

#print axioms transfer_fields
#print axioms withdrawal_fields
end NEL_PaymentFieldCarriers
