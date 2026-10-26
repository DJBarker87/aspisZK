import ARQ_ChoiceCoverage
import SCE_PaddingConditions
import ARS_AccountReplay
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARS_AdaptiveCost
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment SCE_Execution GExq_AccountExperiment

/-- Iterated padding keeps the actual selected second inputs unchanged. -/
theorem second {A : Type} (a : Adversary A) (address : Bytes) (n : Nat)
    (i : FirstInputs A) (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record))
    (final : A) (H : Bytes → State) :
    (eval H ((ARQ_ChoiceCoverage.pad a address n).second i saved post final)).2 =
      (eval H (a.second i saved post final)).2 := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : Adversary A) (address : Bytes) (H : Bytes → State)
    (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : A)
    (first : (eval H (firstCode c hashv copy allocator id (eval H a.first).2)).2 =
      ok (.Ok (saved,post,final)))

include first

theorem outcome (n : Nat) :
    (eval H (account c hashv copy allocator id (ARQ_ChoiceCoverage.pad a address n))).2 =
      (eval H (account c hashv copy allocator id a)).2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ARQ_ChoiceCoverage.pad,SCE_AdaptivePadding.outcome_same c hashv copy allocator id
      (ARQ_ChoiceCoverage.pad a address n) address H saved post final
      (by simpa only [ARQ_ChoiceCoverage.first] using first)]
    exact ih

/-- Exact original work grows by n while complete account outcome is fixed. -/
theorem count (n : Nat) :
    (eval H (account c hashv copy allocator id (ARQ_ChoiceCoverage.pad a address n))).1.length =
      (eval H (account c hashv copy allocator id a)).1.length + n := by
  induction n with
  | zero => simp only [ARQ_ChoiceCoverage.pad,Nat.add_zero]
  | succ n ih =>
    rw [ARQ_ChoiceCoverage.pad,SCE_AdaptivePadding.log_length c hashv copy allocator id
      (ARQ_ChoiceCoverage.pad a address n) address H saved post final
      (by simpa only [ARQ_ChoiceCoverage.first] using first),ih]
    omega

include address

/-- No first-submission budget can bound complete accepted adaptive work.
The world H itself is always query-consistent with its execution. This
obstruction therefore survives the query-restricted ruling. -/
theorem unbounded (Q : Nat)
    (accepted : SCE_Experiment.accepted (eval H (account c hashv copy allocator id a)).2 = true) :
    ∃ b : Adversary A,
      submission b = submission a ∧
      SCE_Experiment.accepted (eval H (account c hashv copy allocator id b)).2 = true ∧
      ARS_AccountReplay.Consistent (account c hashv copy allocator id b) H H ∧
      Q < (eval H (account c hashv copy allocator id b)).1.length ∧
      (eval H b.first).2 = (eval H a.first).2 ∧
      (eval H (b.second (eval H b.first).2 saved post final)).2 =
        (eval H (a.second (eval H a.first).2 saved post final)).2 := by
  let b := ARQ_ChoiceCoverage.pad a address (Q+1)
  refine ⟨b,ARQ_ChoiceCoverage.submitted a address _,?_,?_,?_,?_,?_⟩
  · rw [outcome c hashv copy allocator id a address H saved post final first]
    exact accepted
  · intro x _
    rfl
  · rw [count c hashv copy allocator id a address H saved post final first]
    omega
  · rw [ARQ_ChoiceCoverage.first]
  · rw [ARQ_ChoiceCoverage.first]
    exact second a address _ _ saved post final H

#print axioms second
#print axioms outcome
#print axioms count
#print axioms unbounded
end AspisR1.ARS_AdaptiveCost
end
