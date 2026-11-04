import Lean
import NFY_Part053

set_option autoImplicit false
noncomputable section
namespace NGE_NEL_PaymentFieldCarriers
open NFY_NED_PaymentCohorts

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
end NGE_NEL_PaymentFieldCarriers

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
