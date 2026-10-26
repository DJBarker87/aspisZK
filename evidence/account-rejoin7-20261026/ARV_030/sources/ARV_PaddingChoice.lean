import ARQ_ChoiceCoverage
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARV_PaddingChoice
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment GExq_AccountExperiment

theorem output {A : Type} (a : Adversary A) (address : Bytes) (n : Nat)
    (i : FirstInputs A) (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : A)
    (H : Bytes → State) :
    (eval H ((ARQ_ChoiceCoverage.pad a address n).second i saved post final)).2 =
      (eval H (a.second i saved post final)).2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ARQ_ChoiceCoverage.pad,SCE_AdaptivePadding.choice_eval]
    exact ih

#print axioms output
end AspisR1.ARV_PaddingChoice
end
