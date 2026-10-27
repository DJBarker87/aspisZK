import GExq_OuterGoodStage1
import GExq_OuterGoodStage2
import GExq_RecordTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExq_Caller
open Aeneas Aeneas.Std Result GExq_OuterLower

variable {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)

abbrev sdk := GExp_SecondPair.sdk adapter ops stage finish reserved query geo B std
abbrev child := GExq_ChildCode.execute adapter ops stage finish reserved query geo B std hashv

def first (program : S2W_ExtractionBoundary.Program) (accounts : S2W_ExtractionBoundary.Accounts)
    (data : Slice U8) :=
  lower (child adapter ops stage finish reserved query geo B std hashv)
    (S2W_Outer.stage1_owned (sdk adapter ops stage finish reserved query geo B std)
      S2W_Outer.traceEffects program accounts data)

def second (program : S2W_ExtractionBoundary.Program) (accounts : S2W_ExtractionBoundary.Accounts)
    (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot) :=
  lower (child adapter ops stage finish reserved query geo B std hashv)
    (S2W_Outer.stage2_owned (sdk adapter ops stage finish reserved query geo B std)
      S2W_Outer.traceEffects program accounts data slot)

theorem first_source (law : S2Z.Oracle.NativeBinding
      (sdk adapter ops stage finish reserved query geo B std) hashv)
    (program : S2W_ExtractionBoundary.Program) (accounts : S2W_ExtractionBoundary.Accounts)
    (data : Slice U8) :
    CheckpointBytes5Effect.erase (SdkC_Source.dictionary hashv) ()
      (first adapter ops stage finish reserved query geo B std hashv program accounts data) =
      AdapterRw.r1_pool_adapter.owned.stage1_owned
        (sdk adapter ops stage finish reserved query geo B std) program accounts data := by
  exact (GExq_OuterLower.erasure _ hashv _
    (GExq_ChildCode.erasure adapter ops stage finish reserved query geo B std hashv) _
    (GExq_OuterGoodStage1.stage1 _ hashv law program accounts data)).trans
    (S2W_OuterErasure.stage1_erasure _ program accounts data)

theorem second_source (law : S2Z.Oracle.NativeBinding
      (sdk adapter ops stage finish reserved query geo B std) hashv)
    (program : S2W_ExtractionBoundary.Program) (accounts : S2W_ExtractionBoundary.Accounts)
    (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot) :
    CheckpointBytes5Effect.erase (SdkC_Source.dictionary hashv) ()
      (second adapter ops stage finish reserved query geo B std hashv program accounts data slot) =
      AdapterRw.r1_pool_adapter.owned.stage2_owned
        (sdk adapter ops stage finish reserved query geo B std) program accounts data slot := by
  exact (GExq_OuterLower.erasure _ hashv _
    (GExq_ChildCode.erasure adapter ops stage finish reserved query geo B std hashv) _
    (GExq_OuterGoodStage2.stage2 _ hashv law program accounts data slot)).trans
    (S2W_OuterErasure.stage2_erasure _ program accounts data slot)

#print axioms first_source
#print axioms second_source
end AspisR1.GExq_Caller
end
