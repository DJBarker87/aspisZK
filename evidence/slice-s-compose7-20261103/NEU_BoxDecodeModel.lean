import NEQ_PaymentDecode
set_option autoImplicit false
noncomputable section
namespace NEU_BoxDecodeModel
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open pool_v1.pair_forest_terminal
abbrev Common := PoolV1PairForestTerminalCommonV1

def transferRun (c : Common) (b : Array U8 216#usize) := do
  let decoded ← NEQ_PaymentDecode.transferFull b.to_slice
  match decoded with
  | .Err e => ok (.Err (.Payment e) : core.result.Result PoolV1PairForestTerminalStatementV1 PoolV1PairForestTerminalFormatErrorV1)
  | .Ok p => ok (.Ok (.PrivateTransfer c p))

def withdrawalRun (c : Common) (b : Array U8 216#usize) := do
  let decoded ← NEQ_PaymentDecode.withdrawalFull b.to_slice
  match decoded with
  | .Err e => ok (.Err (.Payment e) : core.result.Result PoolV1PairForestTerminalStatementV1 PoolV1PairForestTerminalFormatErrorV1)
  | .Ok p => ok (.Ok (.Withdrawal c p))

theorem transfer_result_state_effects {State : Type} (c : Common) (b : Array U8 216#usize) (state : State) :
    (transferRun c b,state,([] : List Unit)) =
    (decode_transfer_statement_boxed_v1 c b.to_slice,state,[]) := by
  have same := congrArg (fun x => x.1) (NEQ_PaymentDecode.transfer_result_state_effects b.to_slice state)
  dsimp only at same
  unfold transferRun decode_transfer_statement_boxed_v1
  rw [same,NBP_TransferDecode.fixed]
  cases NBP_PaymentModel.transfer_decoded b <;> rfl

theorem withdrawal_result_state_effects {State : Type} (c : Common) (b : Array U8 216#usize) (state : State) :
    (withdrawalRun c b,state,([] : List Unit)) =
    (decode_withdrawal_statement_boxed_v1 c b.to_slice,state,[]) := by
  have same := congrArg (fun x => x.1) (NEQ_PaymentDecode.withdrawal_result_state_effects b.to_slice state)
  dsimp only at same
  unfold withdrawalRun decode_withdrawal_statement_boxed_v1
  rw [same,NBP_WithdrawalDecode.fixed]
  cases NBP_PaymentModel.withdrawal_decoded b <;> rfl

#print axioms transfer_result_state_effects
#print axioms withdrawal_result_state_effects
end NEU_BoxDecodeModel
