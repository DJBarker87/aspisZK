import SCJ_Projection
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCJ_TableExtension
open FS AspisV8PairedCommitment
variable {I A : Type} [DecidableEq I]
def Extends (small full : Table I A) : Prop :=
  ∀ i answer, small i = some answer → full i = some answer

theorem known {small full : Table I A} (extension : Extends small full)
    (i : I) (present : small i ≠ none) : full i ≠ none := by
  cases value : small i with
  | none => exact False.elim (present value)
  | some a => rw [extension i a value]; exact Option.some_ne_none _

theorem put {small full : Table I A} (extension : Extends small full)
    (i : I) (answer : A) : Extends (AspisV8PairedCommitment.put small i answer)
      (AspisV8PairedCommitment.put full i answer) := by
  intro j a value
  by_cases same : j = i
  · simpa only [AspisV8PairedCommitment.put,if_pos same] using value
  · simp only [AspisV8PairedCommitment.put,if_neg same] at value ⊢
    exact extension j a value

/-- Monotonicity of target membership, with the FULL table's budget cover.
Freshness of the current read is deliberately handled separately. -/
theorem bad {B : Nat} (iv : A) (pred : Fin B → I → Option A) (Q : Nat)
    (i : I) (answer : A) (small full : Table I A)
    (extension : Extends small full) (budget : AllAddressCollision.Small full Q)
    (hit : AllAddressCollision.bad iv pred Q i small answer) :
    AllAddressCollision.bad iv pred Q i full answer := by
  refine ⟨budget,?_⟩
  rcases hit.2 with initial | previous | target
  · exact Or.inl initial
  · obtain ⟨j,value⟩ := previous
    exact Or.inr (Or.inl ⟨j,extension j answer value⟩)
  · obtain ⟨j,b,read,target⟩ := target
    refine Or.inr (Or.inr ⟨j,b,?_,target⟩)
    exact read.elim Or.inl (fun present => Or.inr (known extension b present))

#print axioms known
#print axioms put
#print axioms bad
end AspisR1.SCJ_TableExtension
end
