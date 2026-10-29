import NEE_ValidatorContinuation
set_option autoImplicit false
noncomputable section
namespace NEE_ValidatorContinuationResult
open Aeneas Aeneas.Std Result NBN_StatementResult NED_ErrorCarriers

def model (s : Statement) : core.result.Result Unit NBN_StatementResult.Error :=
  match NED_ValidatorStatus.payment s with
  | .Err e => .Err (.Payment e)
  | .Ok _ => suffix s

theorem payment (s : Statement) : NEE_ValidatorContinuation.payment s =
    ok (NED_CommonValidation.mapPayment (NED_ValidatorStatus.payment s)) := by
  cases s with
  | PrivateTransfer c p => exact NED_TransferEncodingCohort.result p
  | Withdrawal c p => exact NED_WithdrawalEncodingCohort.result p

theorem result (s : Statement) : NEE_ValidatorContinuation.run s =
    ok (NED_LateValidatorCohorts.mapResult toRawPoolV1PairForestTerminalFormatErrorV1 (model s)) := by
  unfold NEE_ValidatorContinuation.run model
  rw [payment]
  cases h : NED_ValidatorStatus.payment s with
  | Err e => rfl
  | Ok bytes =>
    simp only [NED_CommonValidation.mapPayment,bind_tc_ok]
    exact NEE_ValidatorBindings.result s

#print axioms payment
#print axioms result
end NEE_ValidatorContinuationResult
