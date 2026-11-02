import PV_B3P_PanicPatterns571227
namespace PV_B3P_DisabledGate571227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227
set_option autoImplicit false
abbrev BoolStore := Nat → Bool

def assign (store : BoolStore) (slot : Nat) (value : Bool) : BoolStore :=
  fun queried => if queried = slot then value else store queried

theorem assigned_value (store : BoolStore) (slot : Nat) (value : Bool) :
    assign store slot value slot = value := if_pos rfl

/-- Source `if enabled { assertion }` is safe if disabled or its inner test
holds. The inner predicate is deliberately unconstrained here. -/
def gateGuard (store : BoolStore) (slot : Nat) (inner : Bool) : Prop :=
  store slot = false ∨ inner = true
instance (store : BoolStore) (slot : Nat) (inner : Bool) :
    Decidable (gateGuard store slot inner) := inferInstanceAs (Decidable (_ ∨ _))

theorem guard_all_prior_states (store : BoolStore) (slot : Nat) (inner : Bool) :
    gateGuard (assign store slot false) slot inner :=
  Or.inl (assigned_value store slot false)

/-- Applies to every earlier state, even one produced by failing or stateful
world effects, if control reaches the literal assignment at all. Neither the
assertion predicate nor a successful prior Result is assumed. -/
theorem all_prior_states {α : Type} (store : BoolStore) (slot : Nat) (inner : Bool)
    (normal first second : Result α) :
    ¬ diagnostic (gateGuard (assign store slot false) slot inner) ∧
      branch (gateGuard (assign store slot false) slot inner) normal first =
        branch (gateGuard (assign store slot false) slot inner) normal second :=
  (guarded_edge _ normal first second).2 (guard_all_prior_states store slot inner)

/-- Direct source `if false { inner } else { normal }`, with both inner
continuations arbitrary. No formatter or assertion implementation is used. -/
theorem source_branch {α : Type} (store : BoolStore) (slot : Nat)
    (normal first second : Result α) :
    (if assign store slot false slot then first else normal) =
      (if assign store slot false slot then second else normal) := by
  rw [assigned_value]
  rfl

#print axioms assigned_value
#print axioms guard_all_prior_states
#print axioms all_prior_states
#print axioms source_branch
end PV_B3P_DisabledGate571227
