import NBZ_Audit
import NBB_Arithmetic

open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace NCG_CallLog

/-- A logged add/product call carries all three inputs and its result. -/
structure Call where
  old : U64
  coefficient : U32
  scalar : U32
  reply : U64

/-- Substitution at one log entry uses the inherited emitted-fragment theorem.
The semantic association is explicit: an opaque reply alone proves no value law. -/
theorem substitute (c : Call) (terms : Nat)
    (hc : c.coefficient.val < 2^31-1) (hs : c.scalar.val < 2^31-1)
    (ho : NBB_Phase.Bound terms c.old.val)
    (association : S7OwnedP6Scalar.residue_scalar_owned c.old c.coefficient c.scalar false =
      ok c.reply) :
    c.reply.val = c.old.val + c.coefficient.val * c.scalar.val := by
  obtain ⟨out, run, value⟩ := NBB_Arithmetic.add c.old c.coefficient c.scalar terms hc hs ho
  have equal : out = c.reply := Result.ok.inj (run.symm.trans association)
  exact equal ▸ value

/-- Same eight logged entries: structural routing and emitted call semantics
jointly recover all eight coordinate equations. No successful native run is
postulated by this theorem. -/
theorem base_substitution (log : Fin 8 → Call) (terms : Nat)
    (before after : Fin 8 → U64) (coeff : Fin 8 → U32) (scalar : U32)
    (old_input : ∀ k, (log k).old = before k)
    (coefficient_input : ∀ k, (log k).coefficient = coeff k)
    (scalar_input : ∀ k, (log k).scalar = scalar)
    (stores : ∀ k, after k = (log k).reply)
    (hc : ∀ k, (coeff k).val < 2^31-1) (hs : scalar.val < 2^31-1)
    (ho : ∀ k, NBB_Phase.Bound terms (before k).val)
    (association : ∀ k, S7OwnedP6Scalar.residue_scalar_owned
      (log k).old (log k).coefficient (log k).scalar false = ok (log k).reply) :
    ∀ k, (after k).val = (before k).val + (coeff k).val * scalar.val := by
  intro k
  have h := substitute (log k) terms
    (coefficient_input k ▸ hc k) (scalar_input k ▸ hs)
    (old_input k ▸ ho k) (association k)
  rw [stores k, old_input k, coefficient_input k, scalar_input k] at *
  exact h

#print axioms substitute
#print axioms base_substitution
end NCG_CallLog
