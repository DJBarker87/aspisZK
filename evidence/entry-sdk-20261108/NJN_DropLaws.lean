import NJN_GuardModel
set_option autoImplicit false
namespace NJN_GuardModel
/-- Drop consumes exactly its token; it cannot create a second owner. -/
theorem drop_consumes (h : Heap) (t : Nat) (g : Guard) :
    (release h t g).tokens t = none := by simp [release,replace]
/-- An unrelated token is preserved, including its descriptor and mode. -/
theorem drop_other_token (h : Heap) (t j : Nat) (g : Guard) (ne : j ≠ t) :
    (release h t g).tokens j = h.tokens j := by simp [release,replace,ne]
/-- Exclusive live-token destruction restores zero on its SAME cell. -/
theorem exclusive_drop_zero (h : Heap) (t : Nat) (g : Guard)
    (live : Live h t g) (ex : g.exclusive = true) :
    ((release h t g).cells g.cell).counter = 0 := by
  have hc : (h.cells g.cell).counter = -1 := by simpa [Live,ex] using live.2
  simp [release,replace,ex,hc]
/-- Shared drop preserves current data, even after valid intervening operations. -/
theorem drop_payload (h : Heap) (t j : Nat) (g : Guard) :
    ((release h t g).cells j).bytes = (h.cells j).bytes ∧
    ((release h t g).cells j).length = (h.cells j).length := by
  by_cases eq : j = g.cell <;> simp [release,replace,eq]
/-- Shared decrement uses the current same-cell counter, not a saved whole-scope value. -/
theorem shared_drop_counter (h : Heap) (t : Nat) (g : Guard)
    (shared : g.exclusive = false) :
    ((release h t g).cells g.cell).counter = (h.cells g.cell).counter-1 := by
  simp [release,replace,shared]
/-- Drop's library footprint excludes all account metadata and other cells. -/
theorem drop_frame (h : Heap) (t j : Nat) (g : Guard) (ne : j ≠ g.cell) :
    (release h t g).accounts = h.accounts ∧ (release h t g).count = h.count ∧
    (release h t g).cells j = h.cells j := by simp [release,replace,ne]
#print axioms drop_consumes
#print axioms drop_other_token
#print axioms exclusive_drop_zero
#print axioms drop_payload
#print axioms shared_drop_counter
#print axioms drop_frame
end NJN_GuardModel
