import ARQ_LowerTrace
import SCG_WrapperLog
import GExq_Caller
import S2W_OuterOccurrences
import SCG_OuterLog
import SCG_CodeMap
import SCG_FirstCode
import GExq_RecordTrace
import S2W_NativeConsolidation
set_option autoImplicit false
namespace AspisR1.ARQ_FirstOperands
open Aeneas Aeneas.Std Result S2W_Trace _root_.AdapterRw AspisR1.AdapterRw S2W_OuterOccurrences

theorem lifted_log {T : Type} (r : Result T)
    (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State) :
    (AspisV8R19.MemoizedProgramLaw.eval H
      (SdkC_Oracle.program (CheckpointBytes5Effect.liftResult r))).1 = [] := by
  cases r <;> rfl

attribute [local irreducible] _root_.AdapterRw.r1_pool_adapter.owned.require_distinct_accounts
  _root_.AdapterRw.r1_pool_adapter.owned.require_readonly_buffer _root_.AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint
  _root_.AdapterRw.r1_pool_adapter.owned.OwnedAccount.data _root_.AdapterRw.r1_pool_adapter.owned.require_zero
  _root_.AdapterRw.r1_pool_adapter.owned.validate_asq8

theorem first {F C : Type} (adapter : AdapterRw.Ops) (base : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (program : solana_pubkey.Pubkey) (accounts : Slice Cuts.Account)
    (data : Slice U8) (saved : alloc.vec.Vec U8) (log : Log)
    (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
    (execution : run (SCH_IdealSdk.dictionary ⟨adapter,base,stage,finish,reserved,query,geo,B,std⟩ hashv H)
      (S2W_Outer.stage1_owned (SCH_IdealSdk.dictionary ⟨adapter,base,stage,finish,reserved,query,geo,B,std⟩ hashv H)
        S2W_Outer.traceEffects program accounts data) [] = ok (.Ok saved,log)) :
    ∃ semantic pub proof split answer,
      Port1_Driver.decodeSemantic
        (SCH_IdealSdk.dictionary ⟨adapter,base,stage,finish,reserved,query,geo,B,std⟩ hashv H)
        pub = ok (some semantic) ∧
      AdapterRw.first_decoded
        (SCH_IdealSdk.dictionary ⟨adapter,base,stage,finish,reserved,query,geo,B,std⟩ hashv H)
        semantic pub proof split = ok (.Ok saved) ∧
      GExq_RecordTrace.projectLog log = [.first semantic pub proof split answer] ∧
      ARQ_LowerTrace.trace ⟨adapter,base,stage,finish,reserved,query,geo,B,std⟩ hashv H log =
        (AspisV8R19.MemoizedProgramLaw.eval H (SdkC_Oracle.program
          (GExp_FirstCode.code (GExp_FirstPair.base base reserved query geo) B std hashv
            (AspisS6CurrentFirstInstallation.toDigest
              (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
                (GExq_Caller.sdk adapter base stage finish reserved query geo B std)))
            (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof split))).1 := by
  let ops := SCH_IdealSdk.dictionary (⟨adapter,base,stage,finish,reserved,query,geo,B,std⟩ : DrvC_Installation.Configuration F C) hashv H
  change run ops (S2W_Outer.stage1_owned ops S2W_Outer.traceEffects program accounts data) [] = ok (.Ok saved,log) at execution
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
  all_goals refine ⟨_,_,_,_,_,?_,?_,rfl,?_⟩
  all_goals first
  | (unfold Port1_Driver.decodeSemantic; simp_all only [S2W_Trace.invoke,bind_tc_ok]; rfl)
  | (unfold AdapterRw.first_decoded; simp_all only [S2W_Trace.invoke,AdapterRw.mapError,bind_tc_ok]; rfl)
  | skip
  all_goals simp only [ARQ_LowerTrace.trace,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,GExq_Caller.child,GExq_ChildCode.execute,
    lifted_log,SCG_CodeMap.ideal_log,List.nil_append,List.append_nil]
  all_goals rw [SCG_FirstCode.code]
  all_goals rw [show AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops =
    AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
      (GExq_Caller.sdk adapter base stage finish reserved query geo B std) from rfl]

  all_goals exact SCG_CodeMap.ideal_log SdkD_FirstChild.answer _ H

#print axioms lifted_log
#print axioms first
end AspisR1.ARQ_FirstOperands
