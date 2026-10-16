import Aeneas

/-! Pure `List.toChunksExact` facts reused by the row-30 echeck bridge.
Proof bodies are copied from the checked `RecordPayloadPartition` list helpers
(`chunks_partition`, `chunks_remainder_length`, `chunks_full_length`) and
`CanonicalLiteralRow30Chunks.chunks32_count`; this leaf intentionally does not
import parser-generated Types. -/
set_option autoImplicit false

namespace AspisR1.CanonicalLiteralChunkFacts
open Aeneas.Std

theorem chunks32_count {α : Type} (xs : List α) :
    (List.toChunksExact 32 (by decide) xs).1.length = xs.length / 32 := by
  unfold List.toChunksExact
  split
  · simp
    omega
  · rename_i h
    change Nat.succ ((List.toChunksExact 32 (by decide) (xs.drop 32)).1.length) =
      xs.length / 32
    rw [chunks32_count (xs := xs.drop 32)]
    simp only [List.length_drop]
    omega
termination_by xs.length
decreasing_by simp only [List.length_drop]; omega

theorem chunks_partition {α : Type} (n : Nat) (hn : 0 < n) (xs : List α) :
    (List.toChunksExact n hn xs).1.flatten ++ (List.toChunksExact n hn xs).2 = xs := by
  unfold List.toChunksExact
  split
  · simp
  · simp only [List.flatten_cons, List.append_assoc]
    rw [chunks_partition n hn (xs.drop n)]
    exact List.take_append_drop n xs
termination_by xs.length
decreasing_by simp only [List.length_drop]; omega

theorem chunks_remainder_length {α : Type} (n : Nat) (hn : 0 < n) (xs : List α) :
    (List.toChunksExact n hn xs).2.length = xs.length % n := by
  unfold List.toChunksExact
  split
  · rename_i h
    exact (Nat.mod_eq_of_lt h).symm
  · rename_i h
    simp only []
    rw [chunks_remainder_length n hn (xs.drop n), List.length_drop]
    exact (Nat.mod_eq_sub_mod (by omega : n ≤ xs.length)).symm
termination_by xs.length
decreasing_by simp only [List.length_drop]; omega

theorem chunks_full_length {α : Type} (n : Nat) (hn : 0 < n) (xs : List α) :
    ∀ chunk ∈ (List.toChunksExact n hn xs).1, chunk.length = n := by
  unfold List.toChunksExact
  split
  · simp
  · rename_i h
    intro chunk hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · simp [List.length_take, Nat.min_eq_left (by omega : n ≤ xs.length)]
    · exact chunks_full_length n hn (xs.drop n) chunk hc
termination_by xs.length
decreasing_by simp only [List.length_drop]; omega

theorem chunks_cover_of_mod_zero {α : Type} (n : Nat) (hn : 0 < n) (xs : List α)
    (hmod : xs.length % n = 0) :
    (List.toChunksExact n hn xs).2 = [] ∧
      (List.toChunksExact n hn xs).1.flatten = xs := by
  have hrem : (List.toChunksExact n hn xs).2 = [] := by
    apply List.length_eq_zero_iff.mp
    rw [chunks_remainder_length, hmod]
  exact ⟨hrem, by simpa only [hrem, List.append_nil] using chunks_partition n hn xs⟩

theorem chunks32_exact_seven_of_length224 {α : Type} (xs : List α)
    (hlen : xs.length = 224) :
    let chunks := (List.toChunksExact 32 (by decide) xs).1
    chunks.length = 7 ∧
      (List.toChunksExact 32 (by decide) xs).2 = [] ∧
      chunks.flatten = xs ∧
      ∀ chunk ∈ chunks, chunk.length = 32 := by
  dsimp only
  have hcount := chunks32_count xs
  have hcount7 : (List.toChunksExact 32 (by decide) xs).1.length = 7 := by
    rw [hcount, hlen]
  have hmod : xs.length % 32 = 0 := by rw [hlen]
  have hcover := chunks_cover_of_mod_zero 32 (by decide) xs hmod
  refine ⟨hcount7, hcover.1, hcover.2, ?_⟩
  exact chunks_full_length 32 (by decide) xs

#print axioms chunks32_count
#print axioms chunks_partition
#print axioms chunks_remainder_length
#print axioms chunks_full_length
#print axioms chunks_cover_of_mod_zero
#print axioms chunks32_exact_seven_of_length224

end AspisR1.CanonicalLiteralChunkFacts
