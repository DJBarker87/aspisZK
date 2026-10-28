import Std
namespace PV_KStub_AppendCoordinates
/-- Value-only append view; no allocator or pointer claim. -/
def appended {α : Type} (baseBytes tail : Nat → α) (n k : Nat) : α :=
  if k < n then baseBytes k else tail (k-n)
theorem prefix_frame {α : Type} (baseBytes tail : Nat → α) (n k : Nat) (h : k<n) :
    appended baseBytes tail n k = baseBytes k := by simp only [appended, if_pos h]
theorem tail_value {α : Type} (baseBytes tail : Nat → α) (n j : Nat) :
    appended baseBytes tail n (n+j) = tail j := by
  have h : ¬ n+j<n := by omega
  have hs : n+j-n=j := by omega
  simp only [appended, if_neg h, hs]
theorem length_bound (n m : Nat) (hn : n≤2) (hm : m≤1) : n+m≤3 := by omega
#print axioms prefix_frame
#print axioms tail_value
#print axioms length_bound
end PV_KStub_AppendCoordinates

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
