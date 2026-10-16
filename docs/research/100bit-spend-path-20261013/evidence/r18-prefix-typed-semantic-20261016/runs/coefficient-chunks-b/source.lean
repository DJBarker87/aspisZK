import RecordPayloadPartition

/-! The complete chunks retain their original byte offsets. No statement is
made about an ignored remainder. -/
set_option autoImplicit false
namespace AspisR1.ExtractedPrefixChunkOrder
open Aeneas

theorem slice_mem {α : Type} (n : Nat) (hn : 0 < n) (xs : List α) (i : Nat)
    (hi : (i + 1) * n ≤ xs.length) :
    (xs.drop (n * i)).take n ∈ (List.toChunksExact n hn xs).1 := by
  induction i generalizing xs with
  | zero =>
      have hlen : ¬ xs.length < n := by omega
      rw [List.toChunksExact, if_neg hlen]
      simp only [Nat.mul_zero, List.drop_zero, List.mem_cons, true_or]
  | succ i ih =>
      simp only [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul] at hi
      have hlen : ¬ xs.length < n := by omega
      rw [List.toChunksExact, if_neg hlen]
      apply List.mem_cons_of_mem
      have hrest : (i + 1) * n ≤ (xs.drop n).length := by
        rw [List.length_drop]
        omega
      have hmem := ih (xs.drop n) hrest
      simpa only [List.drop_drop, Nat.mul_succ, Nat.add_comm n] using hmem

#print axioms slice_mem
end AspisR1.ExtractedPrefixChunkOrder
