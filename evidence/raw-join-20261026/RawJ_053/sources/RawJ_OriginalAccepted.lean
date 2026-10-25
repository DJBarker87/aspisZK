import RawJ_RecordCuts
import GExq_RootAccepted
import S2W_D189Interpretation
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawJ_OriginalAccepted
open Aeneas Aeneas.Std Result S2W_NativeConsolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.MemoizedProgramLaw

theorem owned_run {A F : Type} (sdk : AdapterRw.Ops) (code : S2W_Trace.Code A)
    (before after : S2W_Trace.Log) (heap : S2Trust.Heap F) (value : A)
    (ran : S2W_D189Interpretation.runOwned sdk code before heap = ok (value,after,heap)) :
    S2W_Trace.run sdk code before = ok (value,after) := by
  rw [S2W_D189Interpretation.owned_account_frame] at ran
  cases actual : S2W_Trace.run sdk code before with
  | fail e => simp only [actual,S2W_Trace.thenResult] at ran; cases ran
  | div => simp only [actual,S2W_Trace.thenResult] at ran; cases ran
  | ok pair =>
    simp only [actual,S2W_Trace.thenResult] at ran
    cases Result.ok.inj ran
    rfl

variable {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)

theorem accepted (law : S2Z.Oracle.NativeBinding
      (GExq_Caller.sdk adapter ops stage finish reserved query geo B std) hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (id : S2W_ExtractionBoundary.Program) (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts)
    (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut) (log : S2W_Trace.Log)
    (ran : S2W_Trace.run (GExq_Caller.sdk adapter ops stage finish reserved query geo B std)
      (S2W_Observation.two (GExq_Caller.sdk adapter ops stage finish reserved query geo B std)
        id accounts1 data1 accounts2 data2 slot) [] = ok (.Ok saved,log))
    (recorded : RawJ_RecordCuts.Recorded f s saved log) :
    eval H (GExq_CallerRecord.program adapter ops stage finish reserved query geo B std hashv
      id accounts1 accounts2 data1 data2 slot) =
      (SdkC_Source.readLog (SdkC_Source.run hashv
        (GExq_CallerRecord.code adapter ops stage finish reserved query geo B std hashv
          id accounts1 accounts2 data1 data2 slot) []).2,
        ok (.Ok saved,[.first f.semantic f.pub f.proof f.split (.Ok saved),
          .second s.pub s.proof s.checkpoint (.Ok ())])) := by
  apply SdkC_Oracle.accepted_exact hashv sha256 H p1 syscall
  rw [SdkC_Source.erasure,← recorded.2]
  exact GExq_CallerRecord.source adapter ops stage finish reserved query geo B std hashv law
    id accounts1 accounts2 data1 data2 slot saved log ran

#print axioms owned_run
#print axioms accepted
end AspisR1.RawJ_OriginalAccepted
end
