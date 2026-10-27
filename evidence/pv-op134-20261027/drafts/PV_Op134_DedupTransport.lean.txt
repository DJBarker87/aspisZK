import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Perm.Basic
namespace R1Z.PV_Op134_DedupTransport
set_option autoImplicit false
/-- The observable row-membership predicate is independent of order and repeats. -/
theorem perm_membership {α : Type} {xs ys : List α} (h : xs.Perm ys) (a : α) :
    a ∈ xs ↔ a ∈ ys := h.mem_iff

theorem dedup_membership {α : Type} [DecidableEq α] (xs : List α) (a : α) :
    a ∈ xs.dedup ↔ a ∈ xs := List.mem_dedup

/-- Boolean membership specifications determine the complete bit observer. -/
theorem observer_eq {α : Type} (xs ys : List α) (left right : α → Bool)
    (hl : ∀ a, left a = true ↔ a ∈ xs)
    (hr : ∀ a, right a = true ↔ a ∈ ys)
    (hm : ∀ a, a ∈ xs ↔ a ∈ ys) : left = right := by
  funext a
  have h := (hl a).trans ((hm a).trans (hr a).symm)
  cases left a <;> cases right a <;> simp_all
#print axioms perm_membership
#print axioms dedup_membership
#print axioms observer_eq
end R1Z.PV_Op134_DedupTransport
