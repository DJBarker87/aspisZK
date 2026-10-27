import RPz7_Hir_FirstChoice
import RPz7_Hir_ChoiceLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_Factory
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (native1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (initial : Store)

abbrev Scheduler (A : Type) := GExq_AccountExperiment.FirstInputs A → alloc.vec.Vec U8 →
  Heap (Nat → Record) → A → Schedule A (Hir_Choice.Submission A)

/-- Both the saved checkpoint's store update and all intervening actions live
inside the SAME second-choice program. post/final are actual wrapper outputs. -/
def choose (scheduler : Scheduler A) (input : GExq_AccountExperiment.FirstInputs A)
    (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : A) :=
  Hir_Choice.program c hashv native1 copy allocator id
    (commit initial (input.entry.handles 2).1 saved) (scheduler input saved post final)

end AspisR1.Hir_Factory
end
