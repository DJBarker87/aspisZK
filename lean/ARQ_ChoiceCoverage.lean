import SCE_AdaptivePadding
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARQ_ChoiceCoverage
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment GExq_AccountExperiment

def pad {A : Type} (a : Adversary A) (address : Bytes) : Nat → Adversary A
  | 0 => a
  | n+1 => SCE_AdaptivePadding.pad (pad a address n) address

theorem first {A : Type} (a : Adversary A) (address : Bytes) (n : Nat) :
    (pad a address n).first = a.first := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem submitted {A : Type} (a : Adversary A) (address : Bytes) (n : Nat) :
    submission (pad a address n) = submission a := by
  simp only [submission,first]

theorem choice_length {A : Type} (a : Adversary A) (address : Bytes) (n : Nat)
    (i : FirstInputs A) (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : A)
    (H : Bytes → State) :
    (eval H ((pad a address n).second i saved post final)).1.length =
      (eval H (a.second i saved post final)).1.length + n := by
  induction n with
  | zero => simp only [pad,Nat.add_zero]
  | succ n ih =>
    rw [pad,SCE_AdaptivePadding.choice_eval,List.length_cons,ih]
    omega

/-- The first-only Rc9 query bound cannot bound all response-driven second
choices, even when the exact first ByteProver stays identical. This is a
carrier/cost obstruction, not a source-accepted attack or a probability bound. -/
theorem unbounded_choice {A : Type} (a : Adversary A) (address : Bytes)
    (i : FirstInputs A) (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : A)
    (H : Bytes → State) (Q : Nat) :
    ¬ ∀ n, (eval H ((pad a address n).second i saved post final)).1.length ≤ Q := by
  intro bound
  have h := bound (Q+1)
  rw [choice_length] at h
  omega

#print axioms first
#print axioms submitted
#print axioms choice_length
#print axioms unbounded_choice
end AspisR1.ARQ_ChoiceCoverage
end
