import F3S_ExactChildren
import F3S_ChildLogs
import F3S_TwoRecords
import F3S_TwoSegments
import RawK_RecordedHead
import RawJ_RecordCuts
import GExq_OuterGoodTwo
import GExq_CallerRecord
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3S_NativeChildren
open Aeneas Aeneas.Std Result GExq_OuterLower

variable {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)

theorem on_pair (law : S2Z.Oracle.NativeBinding
      (GExq_Caller.sdk adapter ops stage finish reserved query geo B std) hashv)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (GExq_Caller.sdk adapter ops stage finish reserved query geo B std) native1 native2 hashv)
    (id : S2W_ExtractionBoundary.Program) (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts)
    (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (saved : alloc.vec.Vec U8)
    (accepted1 : native1 id accounts1 data1=ok (.Ok saved))
    (accepted2 : native2 id accounts2 data2 slot=ok (.Ok ()))
    (f : S2W_NativeConsolidation.FirstCut) (s : S2W_NativeConsolidation.SecondCut) (log : S2W_Trace.Log)
    (ran : S2W_Trace.run (GExq_Caller.sdk adapter ops stage finish reserved query geo B std)
      (S2W_Observation.two (GExq_Caller.sdk adapter ops stage finish reserved query geo B std)
        id accounts1 data1 accounts2 data2 slot) [] = ok (.Ok saved,log))
    (recorded : RawJ_RecordCuts.Recorded f s saved log) :
    SdkC_Source.readLog (SdkC_Source.run hashv
      (GExq_CallerRecord.code adapter ops stage finish reserved query geo B std hashv
        id accounts1 accounts2 data1 data2 slot) []).2=
    SdkC_Source.readLog (SdkC_Source.run hashv
      (GExq_FirstCode.code (GExp_FirstPair.base ops reserved query geo) B std hashv
        (AspisS6CurrentFirstInstallation.toDigest
          (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
            (GExq_Caller.sdk adapter ops stage finish reserved query geo B std)))
        (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split ()) []).2 ++
    SdkC_Source.readLog (SdkC_Source.run hashv
      (GExq_SecondCode.code (GExp_SecondPair.base stage finish reserved query geo) reserved hashv
        (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
          (GExq_Caller.sdk adapter ops stage finish reserved query geo B std))
        s.pub s.proof s.checkpoint ()) []).2 := by
  let sdk := GExq_Caller.sdk adapter ops stage finish reserved query geo B std
  let impl := @GExq_Caller.child F C adapter ops stage finish reserved query geo B std hashv
  let code := S2W_Observation.two sdk id accounts1 data1 accounts2 data2 slot
  have first := (extraction.stage1 id accounts1 data1).symm.trans accepted1
  have second := (extraction.stage2 id accounts2 data2 slot).symm.trans accepted2
  have exactShape := F3S_ExactChildren.exact_children adapter ops stage finish reserved query geo B std
    hashv law id accounts1 accounts2 data1 data2 slot saved first second f s log ran recorded
  have chronology := F3S_Segments.chronological adapter ops stage finish reserved query geo B std hashv log
  rw [exactShape] at chronology
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil] at chronology
  have good := GExq_OuterGoodTwo.two sdk hashv law id accounts1 accounts2 data1 data2 slot
  have ordered := RawK_TraceLogs.ordered sdk hashv impl
    (GExq_ChildCode.erasure adapter ops stage finish reserved query geo B std hashv)
    code good [] log (.Ok saved) ran
  simp only [RawK_TraceLogs.traceLog,List.flatMap_nil,List.nil_append] at ordered
  unfold GExq_CallerRecord.code
  rw [GExq_RecordLog.log]
  have logs := ordered.symm.trans chronology.symm
  rw [F3S_ChildLogs.first] at logs
  exact logs
#print axioms on_pair
end AspisR1.F3S_NativeChildren
end
