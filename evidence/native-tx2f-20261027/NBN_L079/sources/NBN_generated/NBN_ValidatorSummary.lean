import NBN_LateSummary
import NBN_FirstByteDependency
import NBN_StatementCut
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace NBN_ValidatorSummary
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder NBN_StatementResult
attribute [local instance] Classical.propDecidable
abbrev E := NBN_StatementResult.Error
abbrev Transfer := pool_v1.payment_relation.PoolV1PrivateTransferPublicV1
abbrev Withdrawal := pool_v1.payment_relation.PoolV1WithdrawalPublicV1
abbrev PaymentResult := Result (core.result.Result (Array U8 216#usize) PaymentError)
abbrev Encode := NBN_EncoderSummary.Encode

def NBN_Dep_TransferEncode (f : Transfer → PaymentResult) : Prop :=
  ∀ p, f p = pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1 p

def NBN_Dep_WithdrawalEncode (f : Withdrawal → PaymentResult) : Prop :=
  ∀ p, f p = pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1 p

def paymentWith (t : Transfer → PaymentResult) (w : Withdrawal → PaymentResult) : Statement → PaymentResult
  | .PrivateTransfer _ p => t p
  | .Withdrawal _ p => w p

theorem payment_source (t : Transfer → PaymentResult) (w : Withdrawal → PaymentResult)
    (ht : NBN_Dep_TransferEncode t) (hw : NBN_Dep_WithdrawalEncode w) (s : Statement) :
    paymentWith t w s = payment s := by
  cases s <;> first | exact ht _ | exact hw _

def chain (c : NBN_BindingChecks.Common) (p : NBD_TerminalProjection.Parts)
    (tail : Result (core.result.Result Unit E)) : Result (core.result.Result Unit E) :=
  if p.1 ≠ c.master_account then ok (.Err .MasterBindingMismatch)
  else if p.2.1 ≠ c.lane_transition.live_snapshot.deployment_domain then ok (.Err .DeploymentBindingMismatch)
  else if c.lane_transition.live_snapshot.pool ≠ c.master_account then ok (.Err .MasterBindingMismatch)
  else if p.2.2.1 ≠ c.checkpoint_sequence then ok (.Err .CheckpointBindingMismatch)
  else if p.2.2.2.1 ≠ c.historical_global_anchor then ok (.Err .HistoricalAnchorMismatch)
  else tail

theorem chain_pure (c : NBN_BindingChecks.Common) (p : NBD_TerminalProjection.Parts)
    (tail : core.result.Result Unit E) :
    chain c p (ok tail) = ok (NBN_BindingChecks.chain c p tail) := by
  unfold chain NBN_BindingChecks.chain
  repeat' first | rfl | split

def tail (enc : Encode) (s : Statement) : Result (core.result.Result Unit E) := do
  let lane ← NBN_FirstByteDependency.lane enc (parts s).2.2.2.2.1
  match lane with
  | .Err e => ok (.Err (.Account e))
  | .Ok l =>
    if l ≠ (common s).output_lane then ok (.Err .OutputLaneMismatch)
    else do
      let (r,_) ← NBN_LateSummary.run enc (common s).lane_transition NBN_LateResult.zero
      match r with
      | .Err e => ok (.Err (.LaneTransition e))
      | .Ok _ => ok (.Ok ())

theorem tail_source (enc : Encode)
    (lower : NBN_DigestResultDependency.NBN_Dep_DigestEncodeCanonical enc) (s : Statement) :
    tail enc s = ok (NBN_BindingChecks.tail s) := by
  unfold tail
  rw [NBN_FirstByteDependency.lane_source enc lower,NBN_OutputLane.source]
  simp only [bind_tc_ok]
  unfold NBN_BindingChecks.tail
  cases lane : NBN_OutputLane.result (parts s).2.2.2.2.1 with
  | Err e => rfl
  | Ok l =>
    by_cases mismatch : l = (common s).output_lane
    · simp only [mismatch,ne_eq,not_true_eq_false,if_false]
      rw [NBN_LateSummary.source enc lower,NBN_LateResult.source]
      have len : NBN_LateResult.zero.length = 1520 := by
        simp only [NBN_LateResult.zero,Slice.length,Array.to_slice,Array.repeat_val,List.length_replicate]
        rfl
      rw [if_neg (not_not.mpr len)]
      unfold lateStatus
      by_cases index : U64.checked_add (common s).lane_transition.live_snapshot.next_pair_index 1#u64 ≠
          some (common s).lane_transition.candidate_afterstate.next_pair_index
      · simp only [index,if_true,bind_tc_ok]
      · simp only [index,if_false,bind_tc_ok,Aeneas.Std.uncurry]
        cases NBN_LateTail.status (common s).lane_transition <;> rfl
    · simp only [mismatch,ne_eq,not_false_eq_true,if_true]

def run (enc : Encode) (t : Transfer → PaymentResult) (w : Withdrawal → PaymentResult) (s : Statement) :
    Result (core.result.Result Unit E) :=
  if (common s).master_account = zero ∨ (common s).checkpoint_account = zero ∨
      (common s).selected_lane_account = zero then ok (.Err .NonZeroBinding)
  else if 8 ≤ (common s).output_lane.val then ok (.Err .InvalidOutputLane)
  else do
    let pay ← paymentWith t w s
    match pay with
    | .Err e => ok (.Err (.Payment e))
    | .Ok _ => chain (common s) (parts s) (tail enc s)

theorem source (enc : Encode) (t : Transfer → PaymentResult) (w : Withdrawal → PaymentResult)
    (hd : NBN_DigestResultDependency.NBN_Dep_DigestEncodeCanonical enc)
    (ht : NBN_Dep_TransferEncode t) (hw : NBN_Dep_WithdrawalEncode w) (s : Statement) :
    run enc t w s = pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s := by
  rw [NBN_StatementResult.source]
  unfold run result
  dsimp only
  rw [payment_source t w ht hw s,tail_source enc hd s,chain_pure,← NBN_BindingChecks.factor s]
  rfl

#print axioms payment_source
#print axioms chain_pure
#print axioms tail_source
#print axioms source
end NBN_ValidatorSummary
