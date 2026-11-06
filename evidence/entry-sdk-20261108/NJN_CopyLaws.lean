import NJN_GuardModel
set_option autoImplicit false
namespace NJN_GuardModel
/-- A write changes the selected coordinate of the SAME cell carried by the guard. -/
theorem write_selected (h : Heap) (g : Guard) (i v : Nat) :
    ((write h g i v).cells g.cell).bytes i = v := by simp [write,replace]
theorem write_outside (h : Heap) (g : Guard) (i j v : Nat) (ne : j ≠ i) :
    ((write h g i v).cells g.cell).bytes j = (h.cells g.cell).bytes j := by simp [write,replace,ne]
theorem write_cell_frame (h : Heap) (g : Guard) (i j v : Nat) (ne : j ≠ g.cell) :
    (write h g i v).cells j = h.cells j := by simp [write,replace,ne]
theorem write_ownership_frame (h : Heap) (g : Guard) (i v : Nat) :
    (write h g i v).accounts = h.accounts ∧ (write h g i v).tokens = h.tokens ∧
    (write h g i v).count = h.count ∧
    ((write h g i v).cells g.cell).counter = (h.cells g.cell).counter ∧
    ((write h g i v).cells g.cell).length = (h.cells g.cell).length := by simp [write,replace]
/-- Same-cell writes cannot affect a distinct admitted account's data. -/
theorem different_account (h : Heap) (g : Guard) (a i v : Nat)
    (different : (h.accounts a).cell ≠ g.cell) :
    (write h g i v).cells (h.accounts a).cell = h.cells (h.accounts a).cell :=
  write_cell_frame h g i (h.accounts a).cell v different
#print axioms write_selected
#print axioms write_outside
#print axioms write_cell_frame
#print axioms write_ownership_frame
#print axioms different_account
end NJN_GuardModel
