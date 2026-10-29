import PV_DIAG8_Round
set_option autoImplicit false
namespace PV_DIAG8
def publishedIndex (attempts : Nat) : Nat := attempts - 1
/-! Only exact guard implications are claimed until native constructor,
query and publication invariants are associated on the honest family. -/

theorem publication_selected_index (a : Nat) (h : 1 ≤ a ∧ a ≤ 8) : publishedIndex a < 8 := by unfold publishedIndex; omega
#print axioms publication_selected_index
-- NEXT
theorem publication_sub_no_underflow (a : Nat) (h : 1 ≤ a) : a-1+1=a := by omega
#print axioms publication_sub_no_underflow
-- NEXT
theorem publication_callback_bound (k : Nat) (h : k < 8) : k+1 ≤ 8 := by omega
#print axioms publication_callback_bound
-- NEXT
theorem publication_callback_order (entered k : Nat) (h : entered = k) : ¬ k ≠ entered := by omega
#print axioms publication_callback_order
-- NEXT
theorem publication_query_index (i : Nat) (h : i < 22) : i+1 ≤ 22 := by omega
#print axioms publication_query_index
-- NEXT
theorem publication_batch0 : 0 ≤ 10 ∧ 10 ≤ 22 := by decide
#print axioms publication_batch0
-- NEXT
theorem publication_batch1 : 10 ≤ 22 := by decide
#print axioms publication_batch1
-- NEXT
theorem publication_slot_index (b t : Nat) (hb : b < 2) (ht : t < 3) : 3*b+t < 6 := by omega
#print axioms publication_slot_index
-- NEXT
theorem publication_capacity_pad (out nodes cap : Nat) (h : nodes ≤ cap) : out+nodes+cap-nodes = out+cap := by omega
#print axioms publication_capacity_pad
-- NEXT
theorem publication_slot_no_underflow (out nodes cap : Nat) (h : nodes ≤ cap) : nodes ≤ out+nodes+cap := by omega
#print axioms publication_slot_no_underflow
-- NEXT
theorem publication_folded_start (u : Nat) (h : u < 512) : 4*(u/4)+4 ≤ 512 := by omega
#print axioms publication_folded_start
-- NEXT
theorem publication_folded_salt (u : Nat) (h : u < 512) : u/4 < 128 := by omega
#print axioms publication_folded_salt
-- NEXT
theorem publication_opening_values_count : 4*29*32=3712 := by decide
#print axioms publication_opening_values_count
-- NEXT
theorem publication_nodes_guard (nodes cap : Nat) (h : nodes ≤ cap) : ¬ cap < nodes := by omega
#print axioms publication_nodes_guard
end PV_DIAG8
