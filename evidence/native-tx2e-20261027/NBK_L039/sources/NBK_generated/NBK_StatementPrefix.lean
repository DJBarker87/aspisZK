import NBH_Audit
set_option autoImplicit false
noncomputable section
namespace NBK_StatementPrefix
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder
open pool_v1.pair_forest_terminal
abbrev Statement := PoolV1PairForestTerminalStatementV1
abbrev zero : Array U8 32#usize := Array.repeat 32#usize 0#u8
abbrev common := NBD_TerminalProjection.common

theorem zero_rejected (s : Statement)
    (h : (common s).master_account = zero ∨
      (common s).checkpoint_account = zero ∨
      (common s).selected_lane_account = zero) :
    validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Err .NonZeroBinding) := by
  unfold validate_pool_v1_pair_forest_terminal_statement_v1
  rw [NBD_TerminalProjection.source_common]
  simp only [bind_tc_ok, NBH_ArrayEq.source]
  rcases h with h | h | h
  · simp [h]
  · by_cases first : (common s).master_account = zero <;> simp [first,h]
  · by_cases first : (common s).master_account = zero
    · simp [first]
    · by_cases second : (common s).checkpoint_account = zero <;> simp [first,second,h]

theorem lane_rejected (s : Statement)
    (hm : (common s).master_account ≠ zero)
    (hc : (common s).checkpoint_account ≠ zero)
    (hs : (common s).selected_lane_account ≠ zero)
    (lane : 8 ≤ (common s).output_lane.val) :
    validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Err .InvalidOutputLane) := by
  unfold validate_pool_v1_pair_forest_terminal_statement_v1
  rw [NBD_TerminalProjection.source_common]
  simp only [bind_tc_ok, NBH_ArrayEq.source]
  simp only [hm,hc,hs,decide_false,if_false]
  unfold pool_v1.pair_forest_accounts.POOL_V1_PAIR_FOREST_LANE_COUNT
  have cast : core.convert.num.FromUsizeU8.from (common s).output_lane =
      Usize.ofNatCore (common s).output_lane.val (by scalar_tac) := by scalar_tac
  simp only [lift,cast,bind_tc_ok]
  have bound : (Usize.ofNatCore (common s).output_lane.val (by scalar_tac)) ≥ 8#usize := by scalar_tac
  simp only [bound,if_true]

#print axioms zero_rejected
#print axioms lane_rejected
end NBK_StatementPrefix
