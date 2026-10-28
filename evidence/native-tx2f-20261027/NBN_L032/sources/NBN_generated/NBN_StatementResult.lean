import NBN_ArrayNe
import NBN_OutputLane
import NBN_LateResult
import NBK_StatementPrefix
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace NBN_StatementResult
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder
open pool_v1.pair_forest_terminal
attribute [local instance] Classical.propDecidable
abbrev Statement := PoolV1PairForestTerminalStatementV1
abbrev Error := PoolV1PairForestTerminalFormatErrorV1
abbrev PaymentError := pool_v1.payment_relation.PoolV1PaymentStatementFormatError
abbrev common := NBD_TerminalProjection.common
abbrev parts := NBD_TerminalProjection.parts
abbrev zero := NBK_StatementPrefix.zero

def payment (s : Statement) : Result (core.result.Result (Array U8 216#usize) PaymentError) :=
  match s with
  | .PrivateTransfer _ p => pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1 p
  | .Withdrawal _ p => pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1 p

def lateStatus (s : pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) :
    core.result.Result Unit pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1 :=
  if U64.checked_add s.live_snapshot.next_pair_index 1#u64 ≠
      some s.candidate_afterstate.next_pair_index then .Err .AfterstateIndexMismatch
  else NBN_LateTail.status s

def suffix (s : Statement) : core.result.Result Unit Error :=
  let c := common s
  let (pool,deployment,sequence,anchor,nullifier,_) := parts s
  if pool ≠ c.master_account then .Err .MasterBindingMismatch
  else if deployment ≠ c.lane_transition.live_snapshot.deployment_domain then .Err .DeploymentBindingMismatch
  else if c.lane_transition.live_snapshot.pool ≠ c.master_account then .Err .MasterBindingMismatch
  else if sequence ≠ c.checkpoint_sequence then .Err .CheckpointBindingMismatch
  else if anchor ≠ c.historical_global_anchor then .Err .HistoricalAnchorMismatch
  else match NBN_OutputLane.result nullifier with
    | .Err e => .Err (.Account e)
    | .Ok lane => if lane ≠ c.output_lane then .Err .OutputLaneMismatch
      else match lateStatus c.lane_transition with
        | .Err e => .Err (.LaneTransition e)
        | .Ok _ => .Ok ()

def result (s : Statement) : Result (core.result.Result Unit Error) :=
  let c := common s
  if c.master_account = zero ∨ c.checkpoint_account = zero ∨ c.selected_lane_account = zero then
    ok (.Err .NonZeroBinding)
  else if 8 ≤ c.output_lane.val then ok (.Err .InvalidOutputLane)
  else do
    let r ← payment s
    match r with
    | .Err e => ok (.Err (.Payment e))
    | .Ok _ => ok (suffix s)

theorem source (s : Statement) : validate_pool_v1_pair_forest_terminal_statement_v1 s = result s := by
  by_cases hm : (common s).master_account = zero
  · rw [NBK_StatementPrefix.zero_rejected s (Or.inl hm)]
    simp [result,hm]
  · by_cases hc : (common s).checkpoint_account = zero
    · rw [NBK_StatementPrefix.zero_rejected s (Or.inr (Or.inl hc))]
      simp [result,hc]
    · by_cases hs : (common s).selected_lane_account = zero
      · rw [NBK_StatementPrefix.zero_rejected s (Or.inr (Or.inr hs))]
        simp [result,hs]
      · by_cases lane : 8 ≤ (common s).output_lane.val
        · rw [NBK_StatementPrefix.lane_rejected s hm hc hs lane]
          simp [result,hm,hc,hs,lane]
        · unfold validate_pool_v1_pair_forest_terminal_statement_v1
          rw [NBD_TerminalProjection.source_common]
          simp only [NBH_ArrayEq.source,bind_tc_ok,hm,hc,hs,decide_false,if_false]
          have cast : core.convert.num.FromUsizeU8.from (common s).output_lane =
              Usize.ofNatCore (common s).output_lane.val (by scalar_tac) := by scalar_tac
          have small : ¬ (Usize.ofNatCore (common s).output_lane.val (by scalar_tac)) ≥ 8#usize := by scalar_tac
          simp only [lift,cast,bind_tc_ok,pool_v1.pair_forest_accounts.POOL_V1_PAIR_FOREST_LANE_COUNT,small,if_false]
          unfold result
          simp only [hm,hc,hs,lane,not_false_eq_true,or_self,if_false]
          cases s <;> simp only [payment]
          all_goals apply NBN_LateFactor.bind_ext
          all_goals intro pay
          all_goals cases pay with
          | Err e => rfl
          | Ok bytes =>
            simp only [core.result.Result.map_err,bind_tc_ok,
              core.result.Result.Insts.CoreOpsTry.branch]
            rw [NBD_TerminalProjection.source_parts]
            simp only [bind_tc_ok,NBN_ArrayNe.bytes,NBN_ArrayNe.words,
              NBN_OutputLane.source]
            simp only [suffix,common,parts,NBD_TerminalProjection.common,NBD_TerminalProjection.parts,
              Aeneas.Std.uncurry,decide_eq_true_eq,bne_iff_ne]
            simp only [Array.to_slice_mut,lift,bind_tc_ok,Aeneas.Std.uncurry,
              NBN_LateResult.source,Slice.length,Array.to_slice,Array.repeat_val,List.length_replicate]
            simp only [show ¬ ((1520#usize).val ≠ 1520) by decide,if_false]
            simp only [lateStatus]
            repeat' first
              | rfl
              | (split <;> try simp_all only [bind_tc_ok,decide_eq_true_eq,bne_iff_ne])

#print axioms source
end NBN_StatementResult
