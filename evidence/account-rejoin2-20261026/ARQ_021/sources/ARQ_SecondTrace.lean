import ARQ_FirstTrace
import GExq_Caller
import S2W_OuterOccurrences
import SCG_OuterLog
import SCG_CodeMap
import SCG_SecondCode
import GExq_RecordTrace
import S2W_NativeConsolidation
set_option autoImplicit false
namespace AspisR1.ARQ_SecondTrace
open Aeneas Aeneas.Std Result S2W_Trace _root_.AdapterRw AspisR1.AdapterRw S2W_OuterOccurrences

attribute [local irreducible] _root_.AdapterRw.r1_pool_adapter.owned.require_distinct_accounts
  _root_.AdapterRw.r1_pool_adapter.owned.require_readonly_buffer _root_.AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint
  _root_.AdapterRw.r1_pool_adapter.owned.OwnedAccount.data _root_.AdapterRw.r1_pool_adapter.owned.require_zero
  _root_.AdapterRw.r1_pool_adapter.owned.validate_asq8

theorem second {F C : Type} (adapter : AdapterRw.Ops) (base : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (program : solana_pubkey.Pubkey) (accounts : Slice Cuts.Account)
    (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (log : Log)
    (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
    (execution : run (SCH_IdealSdk.dictionary ⟨adapter,base,stage,finish,reserved,query,geo,B,std⟩ hashv H)
      (S2W_Outer.stage2_owned (SCH_IdealSdk.dictionary ⟨adapter,base,stage,finish,reserved,query,geo,B,std⟩ hashv H)
        S2W_Outer.traceEffects program accounts data slot) [] = ok (.Ok (),log)) :
    ∃ pub proof checkpoint answer,
      GExq_RecordTrace.projectLog log = [.second pub proof checkpoint answer] ∧
      ARQ_LowerTrace.trace ⟨adapter,base,stage,finish,reserved,query,geo,B,std⟩ hashv H log =
        (AspisV8R19.MemoizedProgramLaw.eval H (SdkC_Oracle.program
          (GExp_SecondCode.code (GExp_SecondPair.base stage finish reserved query geo) reserved hashv
            (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
                (GExq_Caller.sdk adapter base stage finish reserved query geo B std)) pub proof checkpoint))).1 := by
  let ops := SCH_IdealSdk.dictionary (⟨adapter,base,stage,finish,reserved,query,geo,B,std⟩ : DrvC_Installation.Configuration F C) hashv H
  change run ops (S2W_Outer.stage2_owned ops S2W_Outer.traceEffects program accounts data slot) [] = ok (.Ok (),log) at execution
  simp only [S2W_Outer.stage2_owned,S2W_TraceFacts.run_bind,run_pure,run_lift,run_liftM,
    S2W_Outer.traceEffects,run_perform,S2W_Outer.mapError,then_assoc,then_ok, S2W_Trace.bind] at execution
  repeat' first
  | (solve | cases execution)
  | (fail_if_no_progress simp only [S2W_TraceFacts.run_bind,run_pure,run_lift,run_liftM,run_perform,S2W_Outer.mapError,then_assoc,then_ok, S2W_Trace.bind] at execution)
  | uncase_result
  | head_reduce execution
  | split at execution
  all_goals have logs := congrArg Prod.snd (Result.ok.inj execution)
  all_goals dsimp only at logs
  all_goals rw [← logs]
  all_goals simp only [GExq_RecordTrace.projectLog,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,List.nil_append,List.append_nil,GExq_OuterRecord.project]
  all_goals refine ⟨_,_,_,_,rfl,?_⟩
  all_goals simp only [ARQ_LowerTrace.trace,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,GExq_Caller.child,GExq_ChildCode.execute,
    ARQ_FirstTrace.lifted_log,List.nil_append,List.append_nil]
  all_goals rw [SCG_SecondCode.code]
  all_goals rfl

#print axioms second
end AspisR1.ARQ_SecondTrace
