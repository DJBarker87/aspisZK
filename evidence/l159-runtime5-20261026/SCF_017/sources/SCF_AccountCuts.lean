import SCE_Execution
import SCF_Deletion
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCF_AccountCuts
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open GExq_AccountExperiment SCE_Experiment SCE_Execution

/-- Actual account chronology: deleting the response-driven second choice
preserves every first-read cut already reached by TX1. Second-wrapper
acceptance is NOT required, so rejecting suffixes remain covered. The right
log is a pointwise deletion, not an oracle-free adversary construction. -/
theorem delete_choice {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : Adversary A) (H : Bytes → State)
    (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : A)
    (first : (eval H (firstCode c hashv copy allocator id (eval H a.first).2)).2 =
      .ok (.Ok (saved,post,final)))
    (frame : Bytes)
    (read : FS2.Duplex.Read ((eval H a.first).1 ++
      (eval H (firstCode c hashv copy allocator id (eval H a.first).2)).1) frame) :
    BinRawByteCutRecovery.cut (eval H (account c hashv copy allocator id a)).1 frame =
      BinRawByteCutRecovery.cut
        (((eval H a.first).1 ++
          (eval H (firstCode c hashv copy allocator id (eval H a.first).2)).1) ++
          (eval H (secondCode c hashv allocator id
            (eval H (a.second (eval H a.first).2 saved post final)).2)).1) frame := by
  rw [SCE_Execution.accepted_eval c hashv copy allocator id a H saved post final first]
  dsimp only
  rw [← List.append_assoc, ← List.append_assoc]
  rw [SCE_ReplayTable.cut_append _ _ frame read,
    SCE_ReplayTable.cut_append _ _ frame read]

#print axioms delete_choice
end AspisR1.SCF_AccountCuts
end
