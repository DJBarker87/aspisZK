import RPz8_F3S_Segments
import S2W_OuterOccurrences
import RPz7_GExq_RecordTrace
set_option autoImplicit false
namespace AspisR1.F3S_FirstRecords
open Aeneas Aeneas.Std Result S2W_Trace _root_.AdapterRw AspisR1.AdapterRw S2W_OuterOccurrences

attribute [local irreducible] _root_.AdapterRw.r1_pool_adapter.owned.require_distinct_accounts
  _root_.AdapterRw.r1_pool_adapter.owned.require_readonly_buffer _root_.AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint
  _root_.AdapterRw.r1_pool_adapter.owned.OwnedAccount.data _root_.AdapterRw.r1_pool_adapter.owned.require_zero
  _root_.AdapterRw.r1_pool_adapter.owned.validate_asq8

variable {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)

theorem first_records (sdk : Ops) (program : solana_pubkey.Pubkey)
    (accounts : Slice Cuts.Account) (data : Slice U8) (saved : alloc.vec.Vec U8)
    (log : Log)
    (execution : run sdk (S2W_Outer.stage1_owned sdk S2W_Outer.traceEffects program accounts data)
      [] = ok (.Ok saved,log)) : ∃ semantic pub proof split,
      F3S_Segments.all adapter ops stage finish reserved query geo B std hashv log =
        [(.first semantic pub proof split (.Ok saved),
          RawK_TraceLogs.eventLog hashv (GExq_Caller.child adapter ops stage finish reserved query geo B std hashv)
            (.returned (.op10 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 sdk)
              semantic pub proof split () none) (.Ok saved)))] := by
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
  all_goals simp only [F3S_Segments.all,F3S_Segments.one,List.map_cons,List.map_nil,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,List.nil_append,List.append_nil,GExq_OuterRecord.project]
  all_goals simp_all [core.result.Result.Insts.CoreOpsTry.branch]

#print axioms first_records
end AspisR1.F3S_FirstRecords
