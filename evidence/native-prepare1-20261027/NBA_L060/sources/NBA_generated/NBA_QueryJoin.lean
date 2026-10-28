import NBA_QueryFactor
set_option autoImplicit false
namespace AspisR1.NBA_QueryJoin
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NBA_QueryFactor

theorem bind_same {α β : Type} (m : Result α) (f g : α → Result β)
    (h : ∀ x,f x=g x) : (m >>= f)=(m >>= g) := congrArg (fun k => m >>= k) (funext h)

theorem source (B : QueriesModel.Boundaries) {H : Type}
    (D : aspis_core.Digest32 H) (self : transcript.Transcript H) (row : U8) (payload : Slice U8) :
    QueriesModel.queries B D self row payload=queriesFactored B D self row payload := by
  unfold QueriesModel.queries queriesFactored
  apply bind_same
  intro next
  conv_rhs => rw [distribute]
  unfold materializeThen
  repeat' first
    | apply bind_same; intro x
    | match goal with
      | p : _ × _ ⊢ _ => cases p
    | rfl

#print axioms bind_same
#print axioms source
end AspisR1.NBA_QueryJoin
