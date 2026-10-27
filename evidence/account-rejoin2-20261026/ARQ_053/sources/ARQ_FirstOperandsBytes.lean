import RawJ_FirstTraceFields
import ARQ_FirstOperands
import ARQ_CallFacts
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
namespace AspisR1.ARQ_FirstOperandsBytes
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
      (∃ pa pu raw,
        Slice.index_usize accounts 0#usize = ok pa ∧
        Slice.index_usize accounts 1#usize = ok pu ∧
        AdapterRw.r1_pool_adapter.owned.OwnedAccount.data
          (SCH_IdealSdk.dictionary ⟨adapter,base,stage,finish,reserved,query,geo,B,std⟩ hashv H)
          pa = ok (.Ok raw) ∧
        AdapterRw.r1_pool_adapter.owned.OwnedAccount.data
          (SCH_IdealSdk.dictionary ⟨adapter,base,stage,finish,reserved,query,geo,B,std⟩ hashv H)
          pu = ok (.Ok pub) ∧
        core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
          raw {start := 688#usize,«end» := 58295#usize} = ok proof) ∧
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
  let c : DrvC_Installation.Configuration F C := ⟨adapter,base,stage,finish,reserved,query,geo,B,std⟩
  obtain ⟨sem1,pub1,pf1,k1,answer1,decoded,called,project1,logs⟩ :=
    ARQ_FirstOperands.first adapter base stage finish reserved query geo B std hashv
      program accounts data saved log H execution
  obtain ⟨pa,pu,raw,pub,statement,semantic,proof,split,index0,index1,rawRead,pubRead,
    decode,getter,range,length,first,project2⟩ :=
    RawJ_FirstTraceFields.fields (SCH_IdealSdk.dictionary c hashv H) program accounts data saved log execution
  have equal := (List.cons.inj (project1.symm.trans project2)).1
  obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := GExq_OuterRecord.Event.first.inj equal
  exact ⟨sem1,pub1,pf1,k1,.Ok saved,⟨pa,pu,raw,index0,index1,rawRead,pubRead,range⟩,
    decoded,called,project2,logs⟩

#print axioms first
end AspisR1.ARQ_FirstOperandsBytes
