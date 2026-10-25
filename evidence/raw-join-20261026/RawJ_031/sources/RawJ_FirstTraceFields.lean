import S2W_OuterOccurrences
import GExq_RecordTrace
import S2W_NativeConsolidation
set_option autoImplicit false
namespace AspisR1.RawJ_FirstTraceFields
open Aeneas Aeneas.Std Result S2W_Trace _root_.AdapterRw AspisR1.AdapterRw S2W_OuterOccurrences

attribute [local irreducible] _root_.AdapterRw.r1_pool_adapter.owned.require_distinct_accounts
  _root_.AdapterRw.r1_pool_adapter.owned.require_readonly_buffer _root_.AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint
  _root_.AdapterRw.r1_pool_adapter.owned.OwnedAccount.data _root_.AdapterRw.r1_pool_adapter.owned.require_zero
  _root_.AdapterRw.r1_pool_adapter.owned.validate_asq8

theorem fields (ops : Ops) (program : solana_pubkey.Pubkey)
    (accounts : Slice Cuts.Account) (data : Slice U8) (saved : alloc.vec.Vec U8)
    (log : Log)
    (execution : run ops (S2W_Outer.stage1_owned ops S2W_Outer.traceEffects program accounts data)
      [] = ok (.Ok saved,log)) : ∃ pa pu raw pub statement semantic proof split,
      Slice.index_usize accounts 0#usize = ok pa ∧
      Slice.index_usize accounts 1#usize = ok pu ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops pa = ok (.Ok raw) ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops pu = ok (.Ok pub) ∧
      ops.op47 pub = ok (.Ok statement) ∧
      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
        statement = ok semantic ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        raw {start := 688#usize, «end» := 58295#usize} = ok proof ∧
      AdapterRw.first_decoded ops semantic pub proof split = ok (.Ok saved) ∧
      GExq_RecordTrace.projectLog log = [.first semantic pub proof split (.Ok saved)] := by
  simp only [S2W_Outer.stage1_owned,S2W_TraceFacts.run_bind,run_pure,run_lift,run_liftM,
    S2W_Outer.traceEffects,run_perform,S2W_Outer.mapError,S2W_Outer.first_decoded,then_assoc,then_ok, S2W_Trace.bind] at execution
  repeat' first
  | (solve | cases execution)
  | (fail_if_no_progress simp only [S2W_TraceFacts.run_bind,run_pure,run_lift,run_liftM,run_perform,S2W_Outer.mapError,S2W_Outer.first_decoded,then_assoc,then_ok, S2W_Trace.bind] at execution)
  | uncase_result
  | head_reduce execution
  | split at execution
  all_goals have same := Result.ok.inj execution
  all_goals have values := congrArg Prod.fst same
  all_goals have logs := congrArg Prod.snd same
  all_goals dsimp only at values logs
  all_goals cases core.result.Result.Ok.inj values
  all_goals rw [← logs]
  all_goals simp only [GExq_RecordTrace.projectLog,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,List.nil_append,List.append_nil,GExq_OuterRecord.project]
  all_goals simp_all only [core.result.Result.Insts.CoreOpsTry.branch]
  all_goals simp_all only [S2W_Trace.invoke,
    AdapterRw.Constants.constant_aspis_r1_cost_probe_verifier_PROOF_BYTES,
    AdapterRw.Constants.constant_aspis_statement_pool_v1_pair_terminal_POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES,
    Scalar.checked_add_eq 688#usize 57607#usize 58295#usize (by scalar_tac),
    core.option.Option.ok_or,bind_tc_ok]
  all_goals have checked : Usize.checked_add 688#usize 57607#usize = some 58295#usize := by
    unfold Usize.checked_add core.num.checked_add_UScalar
    rw [Scalar.checked_add_eq 688#usize 57607#usize 58295#usize (by scalar_tac)]
    rfl
  all_goals aesop (add simp [AdapterRw.first_decoded,AdapterRw.observer,checked])

#print axioms fields
end AspisR1.RawJ_FirstTraceFields
