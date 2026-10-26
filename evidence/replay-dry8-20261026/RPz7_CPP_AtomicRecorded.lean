import RPz7_CPP_AtomicRecord
import RPz7_CPP_AtomicSchedule
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_AtomicRecorded
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_ProvenanceModel CPP_AtomicSchedule
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
variable {A B F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (n1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)

def program (before : Store) : Schedule A B → Program Bytes State (Hir_Schedule.Output B × List (CallAt A))
  | .done value => .done ((before,[],value),[])
  | .inspect k => program before (k before)
  | .ask query k => .ask query (fun answer => program before (k answer))
  | .transaction code k =>
    AspisV8R19.OracleProgramOps.bind (CPP_AtomicRecord.program c hashv n1 copy allocator id before code) fun head =>
      AspisV8R19.OracleProgramOps.bind (program head.1.1 (k head.1.2.2)) fun tail =>
        .done ((tail.1.1,head.1.2.1 ++ tail.1.2.1,tail.1.2.2),head.2 ++ tail.2)
end AspisR1.CPP_AtomicRecorded
end
