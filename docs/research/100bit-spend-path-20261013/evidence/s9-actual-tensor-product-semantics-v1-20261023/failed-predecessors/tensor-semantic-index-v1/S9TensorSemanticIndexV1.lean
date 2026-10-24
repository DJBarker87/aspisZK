import S9TensorIndexPartitionV2
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace AspisR1S9TensorSemanticIndexV1
open AspisR1S9TensorIndexPartitionV2

def Processed (n remaining i : Nat) : Prop := i < 4*n ∧ remaining ≤ i % n

/-- In the reverse overwrite loop a new semantic cell is either already
processed, or exactly one of the four source write positions. -/
theorem processed_step_covered (n remaining j i : Nat)
    (hn : 0<n) (hj : j+1=remaining) (hnew : Processed n j i) :
    Processed n remaining i ∨ i=j ∨ i=j+n ∨ i=j+2*n ∨ i=j+3*n := by
  rcases hnew with ⟨hfour,hnew⟩
  by_cases hold : remaining ≤ i%n
  · exact Or.inl ⟨hfour,hold⟩
  · right
    have hm : i%n=j := by omega
    have hq : i/n<4 := (Nat.div_lt_iff_lt_mul hn).2 hfour
    have he := Nat.mod_add_div i n
    rw [hm] at he
    have cases4 : i/n=0 ∨ i/n=1 ∨ i/n=2 ∨ i/n=3 := by omega
    rcases cases4 with h0|h1|h2|h3
    · rw [h0] at he; left; omega
    · rw [h1] at he; right; left; omega
    · rw [h2] at he; right; right; left; omega
    · rw [h3] at he; right; right; right; omega

theorem tensor_write_mod_div (n j digit : Usize) (hn : n.val≤16)
    (hj : j.val<n.val) (hd : digit.val≤3) :
    (tensorIndex n j digit).val % n.val = j.val ∧
      (tensorIndex n j digit).val / n.val = digit.val := by
  have hv := (tensor_index_val n j digit hn hj hd).1
  have hn0 : 0<n.val := by omega
  rw [hv]
  constructor
  · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  · rw [Nat.add_mul_div_right _ _ hn0, Nat.div_eq_of_lt hj, Nat.zero_add]

#print axioms processed_step_covered
#print axioms tensor_write_mod_div
end AspisR1S9TensorSemanticIndexV1
