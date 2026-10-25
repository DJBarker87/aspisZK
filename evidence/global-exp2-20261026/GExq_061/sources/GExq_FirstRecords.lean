import S2W_OuterOccurrences
import GExq_RecordTrace
set_option autoImplicit false
namespace AspisR1.GExq_FirstRecords
open Aeneas Aeneas.Std Result S2W_Trace _root_.AdapterRw AspisR1.AdapterRw S2W_OuterOccurrences

attribute [local irreducible] _root_.AdapterRw.r1_pool_adapter.owned.require_distinct_accounts
  _root_.AdapterRw.r1_pool_adapter.owned.require_readonly_buffer _root_.AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint
  _root_.AdapterRw.r1_pool_adapter.owned.OwnedAccount.data _root_.AdapterRw.r1_pool_adapter.owned.require_zero
  _root_.AdapterRw.r1_pool_adapter.owned.validate_asq8

theorem first_records (ops : Ops) (program : solana_pubkey.Pubkey)
    (accounts : Slice Cuts.Account) (data : Slice U8) (saved : alloc.vec.Vec U8)
    (log : Log)
    (execution : run ops (S2W_Outer.stage1_owned ops S2W_Outer.traceEffects program accounts data)
      [] = ok (.Ok saved,log)) : ∃ semantic pub proof split,
      GExq_RecordTrace.projectLog log =
        [.first semantic pub proof split (.Ok saved)] := by
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
  all_goals refine ⟨_,_,_,_,?_⟩
  all_goals simp [GExq_RecordTrace.projectLog,GExq_OuterRecord.project]

#print axioms first_records
end AspisR1.GExq_FirstRecords
