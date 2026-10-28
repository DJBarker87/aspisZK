import NBK_LiveResult
import JFs_LateConstants
set_option autoImplicit false
noncomputable section
namespace NBK_LatePreflight
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile

theorem option_ne (a b : Option U64) :
    core.cmp.PartialEq.ne.trait_default
      (core.option.Option.Insts.CoreCmpPartialEqOption core.cmp.PartialEqU64) a b =
      ok (decide (a ≠ b)) := by
  cases a <;> cases b
  all_goals simp [core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
    core.option.Option.Insts.CoreCmpPartialEqOption,
    core.option.Option.Insts.CoreCmpPartialEqOption.eq,
    core.cmp.PartialEqU64,core.cmp.impls.PartialEqU64.eq]
  all_goals scalar_tac

theorem wrong_length (s : PoolV1PairLatePublicStatementV1) (output : Slice U8)
    (wrong : output.length ≠ 1520) :
    encode_pool_v1_pair_late_public_statement_v1 s output = ok (.Err .WrongLength,output) := by
  have guard : (Slice.len output != 1520#usize) = true := by scalar_tac
  simp only [encode_pool_v1_pair_late_public_statement_v1,
    AspisR1.JFs_LateConstants.size,bind_tc_ok,guard,if_true]

theorem wrong_index (s : PoolV1PairLatePublicStatementV1) (output : Slice U8)
    (size : output.length = 1520)
    (wrong : U64.checked_add s.live_snapshot.next_pair_index 1#u64 ≠
      some s.candidate_afterstate.next_pair_index) :
    encode_pool_v1_pair_late_public_statement_v1 s output =
      ok (.Err .AfterstateIndexMismatch,output) := by
  have guard : (Slice.len output != 1520#usize) = false := by scalar_tac
  simp only [encode_pool_v1_pair_late_public_statement_v1,
    AspisR1.JFs_LateConstants.size,bind_tc_ok,guard,if_false,lift,option_ne,
    wrong,decide_true,if_true]

#print axioms option_ne
#print axioms wrong_length
#print axioms wrong_index
end NBK_LatePreflight
