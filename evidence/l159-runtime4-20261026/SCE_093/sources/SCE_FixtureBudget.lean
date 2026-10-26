import SCE_JointObserver
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_FixtureBudget
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.MemoizedProgramLaw
open SCE_FixtureSubmission
/-- The same-game fixture's two adversarial choices fit zero queries.
Source wrapper work is still charged separately and acceptance is not inferred. -/
theorem zero (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot) :
    (∀ H, (eval H (adversary data1 data2 slot).first).1.length ≤ 0) ∧
    (∀ i saved post final H,
      (eval H ((adversary data1 data2 slot).second i saved post final)).1.length ≤ 0) := by
  exact ⟨fun _ => Nat.le_refl 0,fun _ _ _ _ _ => Nat.le_refl 0⟩
#print axioms zero
end AspisR1.SCE_FixtureBudget
end
