import RPz7_CPP_AtomicOrigin
import RPz7_CPP_AtomicTrace
import CPP_TraceAppend
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_AtomicSchedule
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_ProvenanceModel
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Explicit transaction grouping: a failing parent discards all of its
successful CPI data effects, while the source program retains every query. -/
inductive Schedule (A B : Type) where
  | done (value : B)
  | inspect (next : Store → Schedule A B)
  | ask (query : Bytes) (next : State → Schedule A B)
  | transaction (code : CPP_Schedule.Schedule A (CPP_Atomic.Reply Unit))
      (next : CPP_Atomic.Reply Unit → Schedule A B)

variable {A B F C : Type}
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)

def run (H : Bytes → State) (before : Store) : Schedule A B → Hir_Schedule.Output B
  | .done value => (before,[],value)
  | .inspect k => run H before (k before)
  | .ask query k => run H before (k (H query))
  | .transaction code k =>
    let head := CPP_Atomic.run n1 n2 copy allocator id H before code
    let tail := run H head.1 (k head.2.2)
    (tail.1,head.2.1 ++ tail.2.1,tail.2.2)

def sites (H : Bytes → State) (before : Store) : Schedule A B → List (CallAt A)
  | .done _ => []
  | .inspect k => sites H before (k before)
  | .ask query k => sites H before (k (H query))
  | .transaction code k =>
    let head := CPP_Atomic.run n1 n2 copy allocator id H before code
    CPP_Atomic.sites n1 n2 copy allocator id H before code ++ sites H head.1 (k head.2.2)

def admissible (H : Bytes → State) (before : Store) : Schedule A B → Prop
  | .done _ => True
  | .inspect k => admissible H before (k before)
  | .ask query k => admissible H before (k (H query))
  | .transaction code k =>
    let head := CPP_Atomic.run n1 n2 copy allocator id H before code
    (CPP_Atomic.committed (CPP_Schedule.run n1 n2 copy allocator id H before code).2.2 →
      Hir_ProvenanceModel.admissible n1 n2 copy allocator id H before (CPP_Schedule.erase code)) ∧
      admissible H head.1 (k head.2.2)

variable (c : DrvC_Installation.Configuration F C) (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)

def program (before : Store) : Schedule A B → Program Bytes State (Hir_Schedule.Output B)
  | .done value => .done (before,[],value)
  | .inspect k => program before (k before)
  | .ask query k => .ask query (fun answer => program before (k answer))
  | .transaction code k =>
    AspisV8R19.OracleProgramOps.bind (CPP_Atomic.program n1 copy allocator id c hashv before code) fun head =>
      AspisV8R19.OracleProgramOps.bind (program head.1 (k head.2.2)) fun tail =>
        .done (tail.1,head.2.1 ++ tail.2.1,tail.2.2)
end AspisR1.CPP_AtomicSchedule
end
