import RPz7_Hir_ScheduleLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_Choice
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

abbrev Submission (A : Type) := Hir_Call.Call A

def input {A : Type} (store : Store) (submission : Submission A) : GExq_AccountExperiment.SecondInputs A :=
  ⟨load store submission.layout,submission.data,submission.slot,submission.state⟩

variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)

/-- The TX2 input is LOADED by this experiment from the final scheduled store.
It is not selected independently and then assumed to match that store. -/
def program (store : Store) (schedule : Schedule A (Submission A)) :
    Program Bytes State (GExq_AccountExperiment.SecondInputs A) :=
  bind (Hir_Schedule.program native1 copy allocator id c hashv store schedule)
    (fun out => .done (input out.1 out.2.2))

theorem selected
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (store : Store) (schedule : Schedule A (Submission A)) :
    (eval H (program c hashv native1 copy allocator id store schedule)).2 =
      let out := run native1 native2 copy allocator id H store schedule
      input out.1 out.2.2 := by
  simp only [program,eval_bind,eval]
  rw [Hir_ScheduleSource.result c hashv native1 native2 copy allocator id extraction sha256 H p1 syscall]

theorem charged (H : Bytes → State) (store : Store) (schedule : Schedule A (Submission A)) :
    (eval H (program c hashv native1 copy allocator id store schedule)).1 =
      (eval H (Hir_Schedule.program native1 copy allocator id c hashv store schedule)).1 := by
  simp only [program,eval_bind,eval,List.append_nil]

#print axioms selected
#print axioms charged
end AspisR1.Hir_Choice
end
