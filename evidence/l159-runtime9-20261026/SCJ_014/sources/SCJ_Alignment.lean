import SCJ_TableExtension
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCJ_Alignment
open FS AspisV8PairedCommitment
variable {I A : Type} [DecidableEq I]
/-- Ordered projection relation sufficient for the charged implication.
Deleted reads may be fresh. Retained projected first reads must ALSO be
first reads in the full trace. Table coverage and the full budget are local
causal invariants, not collision-event or acceptance propositions. -/
inductive Aligned (Q : Nat) : Table I A → Table I A →
    List (I × A) → List (I × A) → Prop
  | nil (small full : Table I A) : Aligned Q small full [] []
  | keep (small full : Table I A) (i : I) (answer : A)
      (left right : List (I × A))
      (extension : SCJ_TableExtension.Extends small full)
      (fresh : small i = none → full i = none)
      (budget : small i = none → AllAddressCollision.Small full Q)
      (rest : Aligned Q (put small i answer) (put full i answer) left right) :
      Aligned Q small full ((i,answer)::left) ((i,answer)::right)
  | drop (small full : Table I A) (i : I) (answer : A)
      (left right : List (I × A))
      (rest : Aligned Q small (put full i answer) left right) :
      Aligned Q small full left ((i,answer)::right)

theorem sublist {Q : Nat} {small full : Table I A} {left right : List (I × A)}
    (alignment : Aligned Q small full left right) : left.Sublist right := by
  induction alignment with
  | nil => exact List.Sublist.refl _
  | keep small full i answer left right extension fresh budget rest ih =>
    exact List.Sublist.cons₂ _ ih
  | drop small full i answer left right rest ih => exact List.Sublist.cons _ ih

#print axioms sublist
end AspisR1.SCJ_Alignment
end
