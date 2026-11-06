import NJN_GuardModel
set_option autoImplicit false
namespace NJN_GuardModel
/-- Entire failed shared acquisition is the unchanged heap and exact SDK error. -/
theorem shared_error (h : Heap) (a t : Nat)
    (bad : ¬ (0 ≤ (h.cells (h.accounts a).cell).counter ∧
      (h.cells (h.accounts a).cell).counter < 9223372036854775807)) :
    acquire h a t false = (h, .error ()) := by simp [acquire, bad]
/-- Entire failed exclusive acquisition is the unchanged heap and exact SDK error. -/
theorem exclusive_error (h : Heap) (a t : Nat)
    (bad : (h.cells (h.accounts a).cell).counter ≠ 0) :
    acquire h a t true = (h, .error ()) := by simp [acquire, bad]
/-- Shared success exports the same cell descriptor and updates exactly one token/counter. -/
theorem shared_ok (h : Heap) (a t : Nat)
    (lo : 0 ≤ (h.cells (h.accounts a).cell).counter)
    (hi : (h.cells (h.accounts a).cell).counter < 9223372036854775807) :
    acquire h a t false =
      ({h with
        cells := (replace h.cells (h.accounts a).cell {h.cells (h.accounts a).cell with counter := (h.cells (h.accounts a).cell).counter+1})
        tokens := replace h.tokens t (some ⟨(h.accounts a).cell,false⟩)},
        .ok ⟨(h.accounts a).cell,false⟩) := by simp [acquire, lo, hi]
/-- Exclusive success has the same descriptor and a -1 counter. -/
theorem exclusive_ok (h : Heap) (a t : Nat)
    (zero : (h.cells (h.accounts a).cell).counter = 0) :
    acquire h a t true =
      ({h with
        cells := (replace h.cells (h.accounts a).cell {h.cells (h.accounts a).cell with counter := -1})
        tokens := replace h.tokens t (some ⟨(h.accounts a).cell,true⟩)},
        .ok ⟨(h.accounts a).cell,true⟩) := by simp [acquire, zero]
/-- Accounts, count, payload and outside cells are never modified by acquisition. -/
theorem acquire_frame (h : Heap) (a t j : Nat) (ex : Bool) :
    (acquire h a t ex).1.accounts = h.accounts ∧
    (acquire h a t ex).1.count = h.count ∧
    ((acquire h a t ex).1.cells j).bytes = (h.cells j).bytes := by
  simp only [acquire]
  split_ifs <;> simp_all [replace]
  all_goals split_ifs <;> simp_all
#print axioms shared_error
#print axioms exclusive_error
#print axioms shared_ok
#print axioms exclusive_ok
#print axioms acquire_frame
end NJN_GuardModel
