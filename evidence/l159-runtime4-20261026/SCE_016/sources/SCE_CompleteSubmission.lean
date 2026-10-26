import SCE_Projection
import RawJ_AccountBudget
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_CompleteSubmission
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open SCE_Experiment F3T_ByteCarrier F3T_Experiment
variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : Adversary A)

/-- Alternative reduction prover retaining the ENTIRE account experiment.
It explicitly pays for both wrappers and adaptive work before returning bytes.
This is not falsely charged as only Q0+Q1 preprocessing. -/
def program : ByteProver :=
  bind (account c hashv copy allocator id a) fun o => .done (submitted o.1)

theorem evaluation (H : Bytes → State) :
    eval H (program c hashv copy allocator id a) =
      ((eval H (account c hashv copy allocator id a)).1,
        (eval H (submission a)).2) := by
  simp only [program,eval_bind,eval,List.append_nil,first_projection,submission_eval]

theorem bytes_same (H : Bytes → State) :
    (eval H (program c hashv copy allocator id a)).2 = (eval H (submission a)).2 := by
  rw [evaluation]

theorem stored_projection (H : Bytes → State) (run : RunView)
    (observed : (eval H (runtime c hashv copy allocator id a)).2 = some run) :
    run.2.1.stored = (eval H (program c hashv copy allocator id a)).2.stored := by
  rw [bytes_same]
  exact SCE_Projection.stored c hashv copy allocator id a H run observed

/-- Uniform all-outcome query bound, derived from the checked account bound.
No accepted native or source call is an input. -/
theorem queries (Q0 Q1 : Nat)
    (prefixBound : ∀ H, (eval H a.first).1.length ≤ Q0)
    (choiceBound : ∀ i saved post final H, (eval H (a.second i saved post final)).1.length ≤ Q1)
    (H : Bytes → State) :
    (eval H (program c hashv copy allocator id a)).1.length ≤ Q0+Q1+1921 := by
  rw [evaluation]
  exact RawJ_AccountBudget.budget c.adapter c.currentBase c.stageBase c.finish c.reserved
    c.query c.geometry c.boundaries c.std hashv copy allocator id a.first a.second
    Q0 Q1 prefixBound choiceBound H

#print axioms evaluation
#print axioms bytes_same
#print axioms stored_projection
#print axioms queries
end AspisR1.SCE_CompleteSubmission
end
