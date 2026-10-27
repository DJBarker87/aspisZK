import RPz7_CPP_AtomicSource
import RPz7_Hir_RecordNative
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_AtomicRecord
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_ProvenanceModel
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Recording observes source replies, and retains only committed-parent
sites for provenance. It never replays a verifier invocation or asks a hash. -/
def keep {A B : Type} (reply : CPP_Atomic.Reply B) (sites : List (CallAt A)) : List (CallAt A) :=
  match reply with
  | .ok (.Ok _) => sites
  | _ => []

variable {A B F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (n1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (before : Store)
    (code : CPP_Schedule.Schedule A (CPP_Atomic.Reply B))

def program : Program Bytes State (CPP_Atomic.Output B × List (CallAt A)) :=
  AspisV8R19.OracleProgramOps.bind
    (Hir_Recorded.program c hashv n1 copy allocator id before (CPP_Schedule.erase code)) fun raw =>
      .done (CPP_Atomic.settle before raw.1,keep raw.1.2.2 raw.2)

theorem erasure (H : Bytes → State) :
    eval H (CPP_Atomic.program n1 copy allocator id c hashv before code) =
      ((eval H (program c hashv n1 copy allocator id before code)).1,
       (eval H (program c hashv n1 copy allocator id before code)).2.1) := by
  rw [CPP_AtomicSource.evaluation,CPP_ProgramErasure.exact,
    Hir_RecordErasure.exact c hashv n1 copy allocator id H before (CPP_Schedule.erase code)]
  simp only [program,eval_bind,eval,List.append_nil]

theorem native (n2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) n1 n2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256) :
    (eval H (program c hashv n1 copy allocator id before code)).2 =
      (CPP_Atomic.run n1 n2 copy allocator id H before code,
       CPP_Atomic.sites n1 n2 copy allocator id H before code) := by
  simp only [program,eval_bind,eval]
  rw [Hir_RecordNative.result c hashv n1 n2 copy allocator id extraction sha256 H p1 syscall]
  rw [← CPP_RunErasure.exact]
  rfl

#print axioms erasure
#print axioms native
end AspisR1.CPP_AtomicRecord
end
