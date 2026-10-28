import Std
namespace PV_KStub_OptionCoordinates
/-- Complete optional byte view, including arbitrary out-of-range coordinates. -/
def view {α : Type} (bytes : Nat → α) (n k : Nat) : Option α :=
  if k < n then some (bytes k) else none
theorem complete_view {α : Type} (a b : Nat → α) (n : Nat)
    (inside : ∀ k, k<n → a k=b k) : ∀ k, view a n k=view b n k := by
  intro k
  by_cases h : k<n
  · simp only [view, if_pos h, inside k h]
  · simp only [view, if_neg h]
theorem outside_none {α : Type} (a : Nat → α) (n k : Nat) (h : n≤k) :
    view a n k=none := by
  have hn : ¬ k<n := by omega
  simp only [view, if_neg hn]
#print axioms complete_view
#print axioms outside_none
end PV_KStub_OptionCoordinates
