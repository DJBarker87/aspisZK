import NED_LateEncodingCohort
import NED_TransferEncodingCohort
import NED_WithdrawalEncodingCohort
set_option autoImplicit false
noncomputable section
namespace NED_ValidatorStatus
open Aeneas Aeneas.Std Result NBN_StatementResult
attribute [local instance] Classical.propDecidable

def payment (s : Statement) : core.result.Result (Array U8 216#usize) PaymentError :=
  match s with
  | .PrivateTransfer _ p => NBP_PaymentModel.transfer_encoded p
  | .Withdrawal _ p => NBP_PaymentModel.withdrawal_encoded p

def status (s : Statement) : core.result.Result Unit NBN_StatementResult.Error :=
  let c := common s
  if c.master_account = zero ∨ c.checkpoint_account = zero ∨ c.selected_lane_account = zero then .Err .NonZeroBinding
  else if 8 ≤ c.output_lane.val then .Err .InvalidOutputLane
  else match payment s with
    | .Err e => .Err (.Payment e)
    | .Ok _ => suffix s

theorem payment_source (s : Statement) : NBN_StatementResult.payment s = ok (payment s) := by
  cases s <;> simp only [NBN_StatementResult.payment,payment,NBP_TransferEncode.result,NBP_WithdrawalEncode.result]

theorem source (s : Statement) :
    AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (status s) := by
  rw [NBN_StatementResult.source]
  unfold NBN_StatementResult.result status
  rw [payment_source]
  dsimp (config := {zeta := true,zetaHave := true}) only
  simp only [bind_tc_ok]
  by_cases zero : (common s).master_account = NBN_StatementResult.zero ∨
      (common s).checkpoint_account = NBN_StatementResult.zero ∨
      (common s).selected_lane_account = NBN_StatementResult.zero
  · simp only [if_pos zero]
  · simp only [if_neg zero]
    by_cases lane : 8 ≤ (common s).output_lane.val
    · simp only [if_pos lane]
    · simp only [if_neg lane]
      cases h : payment s <;> rfl

#print axioms payment_source
#print axioms source
end NED_ValidatorStatus
