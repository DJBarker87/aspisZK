import GExq_OuterGoodTwo
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExq_CallerRecord
open Aeneas Aeneas.Std Result GExq_OuterLower
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

variable {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)

/-- Original complete account and instruction submissions. Child replies drive
all continuations; neither f/s nor an independently selected log is an input. -/
def code (program : S2W_ExtractionBoundary.Program) (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts)
    (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot) :=
  GExq_OuterRecord.record (GExq_Caller.child adapter ops stage finish reserved query geo B std hashv)
    (S2W_Observation.two (GExq_Caller.sdk adapter ops stage finish reserved query geo B std)
      program accounts1 data1 accounts2 data2 slot) []

def program (id : S2W_ExtractionBoundary.Program) (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts)
    (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot) :=
  SdkC_Oracle.program (code adapter ops stage finish reserved query geo B std hashv
    id accounts1 accounts2 data1 data2 slot)

theorem source (law : S2Z.Oracle.NativeBinding
      (GExq_Caller.sdk adapter ops stage finish reserved query geo B std) hashv)
    (id : S2W_ExtractionBoundary.Program) (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts)
    (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (saved : alloc.vec.Vec U8) (log : S2W_Trace.Log)
    (ran : S2W_Trace.run (GExq_Caller.sdk adapter ops stage finish reserved query geo B std)
      (S2W_Observation.two (GExq_Caller.sdk adapter ops stage finish reserved query geo B std)
        id accounts1 data1 accounts2 data2 slot) [] = ok (.Ok saved,log)) :
    CheckpointBytes5Effect.erase (SdkC_Source.dictionary hashv) ()
      (code adapter ops stage finish reserved query geo B std hashv id accounts1 accounts2 data1 data2 slot) =
      ok (.Ok saved,GExq_RecordTrace.projectLog log) := by
  exact GExq_RecordTrace.source _ hashv _
    (GExq_ChildCode.erasure adapter ops stage finish reserved query geo B std hashv) _
    (GExq_OuterGoodTwo.two _ hashv law id accounts1 accounts2 data1 data2 slot) [] log (.Ok saved) ran

#print axioms source
end AspisR1.GExq_CallerRecord
end
