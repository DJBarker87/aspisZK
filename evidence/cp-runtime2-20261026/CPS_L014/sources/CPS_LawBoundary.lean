import CPS_ParentBoundary
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPS_LawBoundary
open AspisV8R19.DuplexFrames CPR_DataPersistence CPS_ParentBoundary

/-- A genuinely adjacent, ordinary pair has a law model for EVERY data value.
Thus even non-vacuity does not tie the runtime projections to source entries. -/
theorem populated (bytes : Bytes) :
    TwoTransactionLaw next ordinary (image bytes) (image bytes) status (loader bytes) ∧
    next false true ∧ ordinary false () ∧ loader bytes true () = some bytes :=
  ⟨law _ _,⟨rfl,rfl⟩,True.intro,rfl⟩

/-- Exact quantifier boundary: if arbitrary runtime projections are appended
to an unchanged root P with ONLY the proposed law, such a theorem supplies Q
already from P alone. This holds with a nonempty adjacent/ordinary pair;
no false-adjacency trick is used. It is NOT a counterexample to P or Q. -/
theorem law_only_eliminates (P Q : Prop)
    (conditional : ∀ (before tentative : Bool → Unit → Image) (success : Bool → Bool)
      (loaded : Bool → Unit → Option Bytes),
      P → TwoTransactionLaw next ordinary before tentative success loaded →
      next false true → ordinary false () → Q) : P → Q := by
  intro original
  exact conditional (image []) (image []) status (loader []) original
    (law [] []) ⟨rfl,rfl⟩ True.intro

/-- Conversely an unconditional source fact needs no persistence law.
Together with law_only_eliminates this identifies the missing source-view
premises rather than assuming that additional law instances constrain them. -/
theorem unconditional_supplies (P Q : Prop) (unconditional : P → Q)
    (before tentative : Bool → Unit → Image) (success : Bool → Bool)
    (loaded : Bool → Unit → Option Bytes)
    (original : P) (runtime : TwoTransactionLaw next ordinary before tentative success loaded) : Q :=
  unconditional original

#print axioms populated
#print axioms law_only_eliminates
#print axioms unconditional_supplies
end AspisR1.CPS_LawBoundary
end
