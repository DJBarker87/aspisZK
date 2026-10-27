import RPz7_GExq_WrapperCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExq_InstalledWrapper
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd

variable {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)

def first {A : Type} (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (allocator : Allocator A) (e : Entry) (id : S2W_ExtractionBoundary.Program) (data : Slice U8) (state : A) :=
  GExq_WrapperCode.first
    (GExq_Caller.first adapter ops stage finish reserved query geo B std hashv id e.first data)
    copy allocator e state

def second {A : Type} (allocator : Allocator A) (e : Entry) (id : S2W_ExtractionBoundary.Program)
    (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (state : A) :=
  GExq_WrapperCode.second
    (GExq_Caller.second adapter ops stage finish reserved query geo B std hashv id (e.second secondSizes) data slot)
    allocator e state

theorem first_source {A : Type} (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (allocator : Allocator A) (e : Entry) (id : S2W_ExtractionBoundary.Program) (data : Slice U8) (state : A)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (GExq_Caller.sdk adapter ops stage finish reserved query geo B std) native1 native2 hashv) :
    CheckpointBytes5Effect.erase (SdkC_Source.dictionary hashv) ()
      (first adapter ops stage finish reserved query geo B std hashv copy allocator e id data state) =
      S2W_D189Wrappers.first native1 copy allocator e id data state := by
  apply GExq_WrapperCode.first_source
  exact (GExq_Caller.first_source adapter ops stage finish reserved query geo B std hashv
    (S2W_DigestExtraction.native_binding _ native1 native2 hashv extraction) id e.first data).trans
    (extraction.stage1 id e.first data).symm

theorem second_source {A : Type} (allocator : Allocator A) (e : Entry) (id : S2W_ExtractionBoundary.Program)
    (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (state : A)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (GExq_Caller.sdk adapter ops stage finish reserved query geo B std) native1 native2 hashv) :
    CheckpointBytes5Effect.erase (SdkC_Source.dictionary hashv) ()
      (second adapter ops stage finish reserved query geo B std hashv allocator e id data slot state) =
      S2W_D189Wrappers.second native2 allocator e id data slot state := by
  apply GExq_WrapperCode.second_source
  exact (GExq_Caller.second_source adapter ops stage finish reserved query geo B std hashv
    (S2W_DigestExtraction.native_binding _ native1 native2 hashv extraction) id (e.second secondSizes) data slot).trans
    (extraction.stage2 id (e.second secondSizes) data slot).symm

#print axioms first_source
#print axioms second_source
end AspisR1.GExq_InstalledWrapper
end
