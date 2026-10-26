import ARQ_Representation
import SCE_RejectedAccount
import RPx_AccountBudget
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARR_Coverage
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment F3T_Experiment
variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : Adversary A) (H : Bytes → State)

/-- An observation of the original account execution. This theorem does not
assert that every independent deployed/native runtime is this observation. -/
theorem observed :
    ∃ run : RunView,
      eval H (runtime c hashv copy allocator id a) =
        ((eval H (account c hashv copy allocator id a)).1,some run) ∧
      run.1 = (eval H (account c hashv copy allocator id a)).1 ∧
      run.2.2 = accepted (eval H (account c hashv copy allocator id a)).2 := by
  rw [runtime_eval]
  exact ⟨_,rfl,rfl,rfl⟩

/-- Issued calls, including repeats and rejected prefixes, cost exactly the
same under the observer. The choice program remains inside account. -/
theorem cost :
    (eval H (runtime c hashv copy allocator id a)).1.length =
      (eval H (account c hashv copy allocator id a)).1.length := by
  rw [runtime_eval]

/-- Uniform installed upper bound counts BOTH adversary phases and both
wrappers, without conditioning on success or removing rejected prefixes. -/
theorem budget (Q0 Q1 : Nat)
    (prefixBound : ∀ H, (eval H a.first).1.length ≤ Q0)
    (choiceBound : ∀ i saved post final H,
      (eval H (a.second i saved post final)).1.length ≤ Q1) :
    (eval H (runtime c hashv copy allocator id a)).1.length ≤ Q0+Q1+1921 := by
  rw [cost]
  exact RPx_AccountBudget.budget c.adapter c.currentBase c.stageBase c.finish
    c.reserved c.query c.geometry c.boundaries c.std hashv copy allocator id a.first a.second
    Q0 Q1 prefixBound choiceBound H

/-- Any functional of the FULL original outcome and chronological log is
preserved. In particular this covers indicators and original cost functions. -/
theorem outcome_law {V : Type}
    (f : List (Bytes × State) × GExq_AccountExperiment.Outcome A → V) :
    f (eval H (Hiq_RecordedJoint.program (account c hashv copy allocator id a)
      ARQ_Observer.project (ARQ_Observer.select c id))).2 =
    f (eval H (account c hashv copy allocator id a)) := by
  exact ARQ_Representation.original_law c hashv copy allocator id f a H

#print axioms observed
#print axioms cost
#print axioms budget
#print axioms outcome_law
end AspisR1.ARR_Coverage
end
