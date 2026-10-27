import Mathlib.Data.List.Sort
set_option autoImplicit false
namespace AspisR1.JGk_TX2_ComparatorTransport

/-- Transport only comparisons reached on the input, then use the key order. -/
theorem map_sort {α : Type} (xs : List α) (key : α → Nat)
    (cmp : α → α → Bool)
    (transport : ∀ a ∈ xs, ∀ b ∈ xs, cmp a b = decide (key a ≤ key b)) :
    (xs.mergeSort cmp).map key = (xs.map key).mergeSort (fun a b => decide (a ≤ b)) :=
  List.map_mergeSort transport
#print axioms map_sort

/-- A sorted permutation identifies the key stream without evaluating mergeSort. -/
theorem key_stream {α : Type} (xs : List α) (key : α → Nat)
    (cmp : α → α → Bool) (ys : List Nat)
    (transport : ∀ a ∈ xs, ∀ b ∈ xs, cmp a b = decide (key a ≤ key b))
    (permutation : (xs.map key).Perm ys) (ordered : ys.Pairwise (· ≤ ·)) :
    (xs.mergeSort cmp).map key = ys := by
  rw [map_sort xs key cmp transport]
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·))
  · exact List.pairwise_mergeSort' (· ≤ ·) _
  · exact ordered
  · exact (List.mergeSort_perm _ _).trans permutation
#print axioms key_stream

/-- Distinct keys remove the installed position tie breaker on this domain. -/
theorem tie_transport {α : Type} (xs : List α) (key : α → Nat)
    (tie : α → α → Prop) [DecidableRel tie]
    (distinct : ∀ a ∈ xs, ∀ b ∈ xs, key a = key b → a = b)
    (reflexive : ∀ a ∈ xs, tie a a) :
    ∀ a ∈ xs, ∀ b ∈ xs,
      decide (key a < key b ∨ key a = key b ∧ tie a b) = decide (key a ≤ key b) := by
  intro a ha b hb
  apply decide_eq_decide.mpr
  constructor
  · intro h
    rcases h with h | ⟨h, _⟩ <;> omega
  · intro h
    by_cases e : key a = key b
    · exact Or.inr ⟨e, by simpa only [distinct a ha b hb e] using reflexive b hb⟩
    · exact Or.inl (by omega)
#print axioms tie_transport
end AspisR1.JGk_TX2_ComparatorTransport
