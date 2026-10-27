import Hir_Choice
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_ChoiceLog
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)

theorem exact
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (store : Store) (schedule : Schedule A (Hir_Choice.Submission A)) :
    (eval H (Hir_Choice.program c hashv native1 copy allocator id store schedule)).1 =
      Hir_ScheduleLog.reads c hashv native1 native2 copy allocator id H store schedule := by
  rw [Hir_Choice.charged]
  exact Hir_ScheduleLog.exact_reads c hashv native1 native2 copy allocator id extraction sha256 H p1 syscall store schedule

/-- Q1 is a bound on the complete choice/scheduler program. The SAME bound
therefore covers every successful read in rejected intervening native calls. -/
theorem budget (store : Store) (schedule : Schedule A (Hir_Choice.Submission A))
    (Q1 : Nat) (bound : ∀ H, (eval H (Hir_Choice.program c hashv native1 copy allocator id store schedule)).1.length ≤ Q1)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    :
    (Hir_ScheduleLog.reads c hashv native1 native2 copy allocator id H store schedule).length ≤ Q1 := by
  rw [← exact c hashv native1 native2 copy allocator id extraction sha256 H p1 syscall store schedule]
  exact bound H

#print axioms exact
#print axioms budget
end AspisR1.Hir_ChoiceLog
end
