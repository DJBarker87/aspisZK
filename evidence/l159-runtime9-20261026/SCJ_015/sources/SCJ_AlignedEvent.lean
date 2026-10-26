import SCJ_Alignment
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCJ_AlignedEvent
open FS AspisV8PairedCommitment
variable {I A : Type} [DecidableEq I]
/-- The event direction needed by the bound; equality is unnecessary. -/
theorem hits {B : Nat} (iv : A) (pred : Fin B → I → Option A) (Q : Nat)
    {small full : Table I A} {left right : List (I × A)}
    (alignment : SCJ_Alignment.Aligned Q small full left right) :
    hitsBad (AllAddressCollision.bad iv pred Q) small left →
      hitsBad (AllAddressCollision.bad iv pred Q) full right := by
  induction alignment with
  | nil => intro impossible; exact False.elim impossible
  | keep small full i answer left right extension fresh budget rest ih =>
    intro hit
    rcases hit with head | tail
    · exact Or.inl ⟨fresh head.1,
        SCJ_TableExtension.bad iv pred Q i answer small full extension (budget head.1) head.2⟩
    · exact Or.inr (ih tail)
  | drop small full i answer left right rest ih =>
    intro hit
    exact Or.inr (ih hit)

#print axioms hits
end AspisR1.SCJ_AlignedEvent
end
