import RPz8_ARU_WrapperSource
import RPz8_ART_NativeAgreement
import RPz8_ART_WrapperExact
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARV_NativePartial
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

variable {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (GExq_Caller.sdk adapter ops stage finish reserved query geo B std) native1 native2 hashv)
    (H : Bytes → State) (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv H)

include extraction syscall

theorem first {A : Type}
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (e : Entry) (id : S2W_ExtractionBoundary.Program)
    (data : Slice U8) (state : A) (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : A)
    (yes : S2W_D189Wrappers.first native1 copy allocator e id data state = ok (.Ok (saved,post,final))) :
    (eval H (ART_PartialAccount.wrapper hashv
      (GExq_InstalledWrapper.first adapter ops stage finish reserved query geo B std hashv
        copy allocator e id data state))).2 = ok (.Ok (saved,post,final)) := by
  rw [ART_WrapperExact.execution hashv H _ (ART_NativeAgreement.issued hashv H syscall _)]
  exact ARU_WrapperSource.first adapter ops stage finish reserved query geo B std hashv
    copy allocator e id data state native1 native2 extraction saved post final yes

theorem second {A : Type}
    (allocator : Allocator A) (e : Entry) (id : S2W_ExtractionBoundary.Program)
    (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (state : A)
    (post : Heap (Nat → Record)) (final : A)
    (yes : S2W_D189Wrappers.second native2 allocator e id data slot state = ok (.Ok (post,final))) :
    (eval H (ART_PartialAccount.wrapper hashv
      (GExq_InstalledWrapper.second adapter ops stage finish reserved query geo B std hashv
        allocator e id data slot state))).2 = ok (.Ok (post,final)) := by
  rw [ART_WrapperExact.execution hashv H _ (ART_NativeAgreement.issued hashv H syscall _)]
  exact ARU_WrapperSource.second adapter ops stage finish reserved query geo B std hashv
    allocator e id data slot state native1 native2 extraction post final yes

#print axioms first
#print axioms second
end AspisR1.ARV_NativePartial
end
