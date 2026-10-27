import SCE_AdaptivePadding
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_PaddingBudget
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment SCE_AdaptivePadding

/-- The padding diagnostic pays for its extra oracle call; it is never
asserted to remain in an unchanged finite query budget. -/
theorem choice_bound {A : Type} (a : Adversary A) (address : Bytes) (Q1 : Nat)
    (choice : ∀ i saved post final H, (eval H (a.second i saved post final)).1.length ≤ Q1) :
    ∀ i saved post final H, (eval H ((pad a address).second i saved post final)).1.length ≤ Q1+1 := by
  intro i saved post final H
  rw [choice_eval]
  simp only [List.length_cons]
  exact Nat.add_le_add_right (choice i saved post final H) 1

theorem prefix_same {A : Type} (a : Adversary A) (address : Bytes) :
    (pad a address).first = a.first := rfl

#print axioms choice_bound
#print axioms prefix_same
end AspisR1.SCE_PaddingBudget
end
