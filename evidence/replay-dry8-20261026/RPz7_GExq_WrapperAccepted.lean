import RPz7_GExq_InstalledWrapper
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExq_WrapperAccepted
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.MemoizedProgramLaw

variable {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)

theorem first {A : Type} (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (allocator : Allocator A) (e : Entry) (id : S2W_ExtractionBoundary.Program) (data : Slice U8) (state : A)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (GExq_Caller.sdk adapter ops stage finish reserved query geo B std) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : A)
    (accepted : S2W_D189Wrappers.first native1 copy allocator e id data state = ok (.Ok (saved,post,final))) :
    let code := GExq_InstalledWrapper.first adapter ops stage finish reserved query geo B std hashv copy allocator e id data state
    eval H (SdkC_Oracle.program code) =
      (SdkC_Source.readLog (SdkC_Source.run hashv code []).2,ok (.Ok (saved,post,final))) := by
  apply SdkC_Oracle.accepted_exact hashv sha256 H p1 syscall
  rw [SdkC_Source.erasure]
  exact (GExq_InstalledWrapper.first_source adapter ops stage finish reserved query geo B std hashv
    copy allocator e id data state native1 native2 extraction).trans accepted

theorem second {A : Type} (allocator : Allocator A) (e : Entry) (id : S2W_ExtractionBoundary.Program)
    (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (state : A)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (GExq_Caller.sdk adapter ops stage finish reserved query geo B std) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (post : Heap (Nat → Record)) (final : A)
    (accepted : S2W_D189Wrappers.second native2 allocator e id data slot state = ok (.Ok (post,final))) :
    let code := GExq_InstalledWrapper.second adapter ops stage finish reserved query geo B std hashv allocator e id data slot state
    eval H (SdkC_Oracle.program code) =
      (SdkC_Source.readLog (SdkC_Source.run hashv code []).2,ok (.Ok (post,final))) := by
  apply SdkC_Oracle.accepted_exact hashv sha256 H p1 syscall
  rw [SdkC_Source.erasure]
  exact (GExq_InstalledWrapper.second_source adapter ops stage finish reserved query geo B std hashv
    allocator e id data slot state native1 native2 extraction).trans accepted

#print axioms first
#print axioms second
end AspisR1.GExq_WrapperAccepted
end
