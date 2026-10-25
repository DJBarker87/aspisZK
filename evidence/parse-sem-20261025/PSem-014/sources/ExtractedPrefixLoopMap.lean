import ExtractedPrefixFieldAgreement

/-! Finite-state loop transport for the concrete parser carrier agreement.
The decreasing measure is an explicit hypothesis, not a termination axiom. -/
namespace AspisR1.ExtractedPrefixLoopMap
open Aeneas Aeneas.Std Result ControlFlow
open ExtractedPrefixFieldAgreement

def mapControl {σ α β : Type} (f : α → β) : ControlFlow σ α → ControlFlow σ β
  | cont next => cont next
  | done value => done (f value)

/-- Transport both normal returns and failures when every continuation strictly
reduces a natural measure. No claim is made for arbitrary divergent loops. -/
theorem loop_map {σ α β : Type} (f : α → β)
    (left : σ → Result (ControlFlow σ α))
    (right : σ → Result (ControlFlow σ β)) (measure : σ → Nat)
    (body_eq : ∀ state, mapResult (mapControl f) (left state) = right state)
    (decreases : ∀ state next, left state = ok (cont next) →
      measure next < measure state) (state : σ) :
    mapResult f (loop left state) = loop right state := by
  conv_lhs => rw [loop]
  conv_rhs => rw [loop]
  rw [← body_eq state]
  cases h : left state with
  | fail e => rfl
  | div => rfl
  | ok step =>
    cases step with
    | done value => rfl
    | cont next =>
      change mapResult f (loop left next) = loop right next
      exact loop_map f left right measure body_eq decreases next
termination_by measure state
decreasing_by exact decreases state next h

end AspisR1.ExtractedPrefixLoopMap

#print axioms AspisR1.ExtractedPrefixLoopMap.loop_map
