import GExq_CallerRecord
import GExq_TwoRecords
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExq_NativeRecords
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

variable {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)

/-- Native acceptance produces the containing caller's ordered log and the
exact same-world oracle evaluation. No independent source success is assumed. -/
theorem accepted (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (GExq_Caller.sdk adapter ops stage finish reserved query geo B std) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (id : S2W_ExtractionBoundary.Program) (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts)
    (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (saved : alloc.vec.Vec U8)
    (accepted1 : native1 id accounts1 data1 = ok (.Ok saved))
    (accepted2 : native2 id accounts2 data2 slot = ok (.Ok ())) :
    ∃ log semantic pub1 proof1 split pub2 proof2 checkpoint,
      S2W_Trace.run (GExq_Caller.sdk adapter ops stage finish reserved query geo B std)
        (S2W_Observation.two (GExq_Caller.sdk adapter ops stage finish reserved query geo B std)
          id accounts1 data1 accounts2 data2 slot) [] = ok (.Ok saved,log) ∧
      eval H (GExq_CallerRecord.program adapter ops stage finish reserved query geo B std hashv
        id accounts1 accounts2 data1 data2 slot) =
        (SdkC_Source.readLog (SdkC_Source.run hashv
          (GExq_CallerRecord.code adapter ops stage finish reserved query geo B std hashv
            id accounts1 accounts2 data1 data2 slot) []).2,
          ok (.Ok saved,[.first semantic pub1 proof1 split (.Ok saved),
            .second pub2 proof2 checkpoint (.Ok ())])) := by
  obtain ⟨log,semantic,pub1,proof1,split,pub2,proof2,checkpoint,ran,shape⟩ :=
    GExq_TwoRecords.accepted _ id accounts1 accounts2 data1 data2 slot saved
      ((extraction.stage1 id accounts1 data1).symm ▸ accepted1)
      ((extraction.stage2 id accounts2 data2 slot).symm ▸ accepted2)
  refine ⟨log,semantic,pub1,proof1,split,pub2,proof2,checkpoint,ran,?_⟩
  apply SdkC_Oracle.accepted_exact hashv sha256 H p1 syscall
  rw [SdkC_Source.erasure]
  rw [← shape]
  exact GExq_CallerRecord.source adapter ops stage finish reserved query geo B std hashv
    (S2W_DigestExtraction.native_binding _ native1 native2 hashv extraction)
    id accounts1 accounts2 data1 data2 slot saved log ran

#print axioms accepted
end AspisR1.GExq_NativeRecords
end
