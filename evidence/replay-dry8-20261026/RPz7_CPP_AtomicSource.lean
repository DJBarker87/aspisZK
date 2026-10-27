import RPz7_CPP_AtomicLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_AtomicSource
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers CPP_Atomic
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
variable {A B F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (n1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (before : Store) (code : CPP_Schedule.Schedule A (CPP_Atomic.Reply B))

/-- Even when the entire transaction aborts, every reached hash read remains
in exactly the same source log. Rollback changes the bank state projection. -/
theorem evaluation (H : Bytes → State) :
    eval H (CPP_Atomic.program n1 copy allocator id c hashv before code) =
      ((eval H (CPP_Schedule.program n1 copy allocator id c hashv before code)).1,
        settle before (eval H (CPP_Schedule.program n1 copy allocator id c hashv before code)).2) := by
  simp only [CPP_Atomic.program,eval_bind,eval,List.append_nil]

theorem native (n2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) n1 n2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256) :
    (eval H (CPP_Atomic.program n1 copy allocator id c hashv before code)).2 =
      CPP_Atomic.run n1 n2 copy allocator id H before code := by
  rw [evaluation]
  change settle before _ = settle before _
  rw [CPP_ProgramErasure.exact,
    Hir_ScheduleSource.result c hashv n1 n2 copy allocator id extraction sha256 H p1 syscall]
  rw [CPP_RunErasure.exact]

#print axioms evaluation
#print axioms native
end AspisR1.CPP_AtomicSource
end
