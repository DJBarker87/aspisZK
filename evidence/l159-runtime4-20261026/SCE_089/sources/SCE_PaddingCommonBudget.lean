import SCE_PaddingBudget
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_PaddingCommonBudget
open Aeneas Aeneas.Std S2Trust S2W_D189Entry
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.MemoizedProgramLaw
open SCE_Experiment SCE_AdaptivePadding
/-- Both adversaries fit ONE common finite allowance. No free extra query
is asserted: the common second-choice allowance is Q1+1. -/
theorem both {A : Type} (a : Adversary A) (address : Bytes) (Q1 : Nat)
    (choice : ∀ i saved post final H, (eval H (a.second i saved post final)).1.length ≤ Q1) :
    (∀ i saved post final H, (eval H (a.second i saved post final)).1.length ≤ Q1+1) ∧
    (∀ i saved post final H, (eval H ((pad a address).second i saved post final)).1.length ≤ Q1+1) := by
  exact ⟨fun i saved post final H => (choice i saved post final H).trans (Nat.le_succ Q1),
    SCE_PaddingBudget.choice_bound a address Q1 choice⟩
#print axioms both
end AspisR1.SCE_PaddingCommonBudget
end
