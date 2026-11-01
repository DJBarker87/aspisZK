import NEE_ValidatorGate
set_option autoImplicit false
noncomputable section
namespace NEE_ValidatorContinuation
open Aeneas Aeneas.Std Result NBN_StatementResult AspisR1AdapterReconstruct
open NED_ErrorCarriers
abbrev RawPayment := Result (core.result.Result (Array U8 216#usize)
  aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError)

def payment (s : Statement) : RawPayment :=
  match s with
  | .PrivateTransfer _ p => aspis_statement.pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1
      (NED_PaymentCohorts.toRawTransfer p)
  | .Withdrawal _ p => aspis_statement.pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1
      (NED_PaymentCohorts.toRawWithdrawal p)

def run (s : Statement) : NEE_RawValidatorPrefix.R := do
  let r ← payment s
  match r with
  | .Err e => ok (.Err (.Payment e))
  | .Ok _ => NED_RawValidatorBindings.run s

/-- The complete raw continuation, with payment still left as an arbitrary
child Result. No source child is unfolded and no successful-parent premise is used. -/
theorem source_factor (s : Statement) :
    NEE_RawValidatorPrefix.continuation (NED_ReconstructCarriers.toRaw s)
      (NED_ReconstructCarriers.toRawCommon (common s)) = run s := by
  cases s with
  | PrivateTransfer c p =>
    unfold NEE_RawValidatorPrefix.continuation run payment
    rw [NED_StatementCarrierFields.transfer]
    apply NBN_LateFactor.bind_ext
    intro r
    cases r <;> rfl
  | Withdrawal c p =>
    unfold NEE_RawValidatorPrefix.continuation run payment
    rw [NED_StatementCarrierFields.withdrawal]
    apply NBN_LateFactor.bind_ext
    intro r
    cases r <;> rfl

#print axioms source_factor
end NEE_ValidatorContinuation
