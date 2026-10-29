import PV_DIAG8_Cursor
set_option autoImplicit false
namespace PV_DIAG8
/-! Bounds for prover::round and fold. PERM=[0,3,2,1]; no field
normalization and no formatted assertion operand is evaluated. -/
def roundPerm (t : Nat) : Nat := if t = 0 then 0 else if t = 1 then 3 else if t = 2 then 2 else 1
def foldedLength (n : Nat) : Nat := n / 4

theorem round_perm_bound (t : Nat) : roundPerm t ≤ 3 := by unfold roundPerm; split <;> (try split) <;> (try split) <;> omega
#print axioms round_perm_bound
-- NEXT
theorem round_coeff_bound (s t : Nat) (hs : s < 4) : s + roundPerm t < 7 := by have := round_perm_bound t; omega
#print axioms round_coeff_bound
-- NEXT
theorem round_query_bound (n d s : Nat) (hd : d < n / 4) (hs : s < 4) : 4*d+s < n := by omega
#print axioms round_query_bound
-- NEXT
theorem round_weight_bound (n d t : Nat) (hd : d < n / 4) (ht : t < 4) : 4*d+t < n := round_query_bound n d t hd ht
#print axioms round_weight_bound
-- NEXT
theorem round_equal_shape (q w : Nat) (h : q = w) : ¬ q ≠ w := by omega
#print axioms round_equal_shape
-- NEXT
theorem round_fold_equal (q w : Nat) (h : q = w) : foldedLength q = foldedLength w := congrArg foldedLength h
#print axioms round_fold_equal
-- NEXT
theorem round_fold_nonincrease (n : Nat) : foldedLength n ≤ n := Nat.div_le_self _ _
#print axioms round_fold_nonincrease
-- NEXT
theorem round_fold_index0 (n i : Nat) (h : i < n/4) : 4*i < n := by omega
#print axioms round_fold_index0
-- NEXT
theorem round_fold_index1 (n i : Nat) (h : i < n/4) : 4*i+1 < n := by omega
#print axioms round_fold_index1
-- NEXT
theorem round_fold_index2 (n i : Nat) (h : i < n/4) : 4*i+2 < n := by omega
#print axioms round_fold_index2
-- NEXT
theorem round_fold_index3 (n i : Nat) (h : i < n/4) : 4*i+3 < n := by omega
#print axioms round_fold_index3
-- NEXT
theorem round_messages_lane (l : Nat) (h : l < 26) : l < 29 := by omega
#print axioms round_messages_lane
-- NEXT
theorem round_messages_aux : 26 < 29 ∧ 27 < 29 ∧ 28 < 29 := by decide
#print axioms round_messages_aux
-- NEXT
theorem round_row_increment (r : Nat) (h : r < 1024) : r+1 ≤ 1024 ∧ r+1 < 2^32 := by omega
#print axioms round_row_increment
end PV_DIAG8
