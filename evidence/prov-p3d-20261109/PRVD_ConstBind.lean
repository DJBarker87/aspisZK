-- PCVD_ item 1: the generic constant-binding facts used by the per-module shims.
-- In the cross-crate fresh emissions a constant of another crate (aspis_core::field::QM31::ZERO, ::ONE, M31::ONE, P, ...) is an
-- external `axiom X : Result T`; the gate carries the pure value `X : T`.  The shim `X := ok <gate X>` is an INSTANTIATION of the
-- external, not a proof about it.  The lemmas say what the instantiation does and that the result is independent of how it is spelled:
-- for any binding c with `c = ok v`, a monadic use `let q ← c; k q` is `k v`.
-- The binding `c = ok v` itself (external axiom = transparent aspis_core definition) is a hypothesis of every shim theorem and is
-- recorded in PCVD_CLASSIFICATION.json (row CONSTANT_BINDING); the transparent aspis_core emissions PCQF_E007/E013 (QM31.ZERO, ONE)
-- and PCQF_E002..E006 (field.P) carry the pure values with text identical to the gate constants.
import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error

namespace PRVD

theorem const_bind {α β : Type} (v : α) (k : α → Result β) :
    (Bind.bind (ok v : Result α) k) = k v := rfl

theorem const_bind_of_eq {α β : Type} {c : Result α} {v : α} (h : c = ok v) (k : α → Result β) :
    (Bind.bind c k) = k v := by subst h; rfl

/-- a fresh function with a hoisted constant parameter equals a gate function without it exactly at the instantiated value:
    `f a = g` iff the equation holds pointwise (the hoisted parameter is NOT universally quantified; only a = the gate constant is claimed). -/
theorem hoisted_param_eq {α β γ : Type} (f : α → β → γ) (g : β → γ) (a : α) :
    (f a = g) ↔ ∀ b, f a b = g b :=
  ⟨fun h b => by rw [h], fun h => funext h⟩

/-- the instantiation is not vacuous for the shimmed constant: two different bindings both satisfying `= ok v` give equal uses -/
theorem const_bind_unique {α β : Type} {c c' : Result α} {v : α} (h : c = ok v) (h' : c' = ok v) (k : α → Result β) :
    (Bind.bind c k) = (Bind.bind c' k) := by rw [const_bind_of_eq h, const_bind_of_eq h']

end PRVD
#print axioms PRVD.const_bind
#print axioms PRVD.const_bind_of_eq
#print axioms PRVD.hoisted_param_eq
#print axioms PRVD.const_bind_unique
