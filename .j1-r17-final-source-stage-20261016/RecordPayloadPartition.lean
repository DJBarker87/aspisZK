import ExtractedRecordFraming

/-! Exact-chunk coverage for successfully framed record payloads. These
lemmas concern the cached Aeneas list model and the extracted row table;
they do not assert Rust iterator refinement or field validation. -/
set_option autoImplicit false
namespace AspisR1.RecordPayloadPartition
open Aeneas Aeneas.Std Result

theorem table_size_mod (row tag : U8) (size : Usize)
    (h : ExtractedRowShape.table row = some (tag, size)) :
    size.val % 32 = 0 := by
  unfold ExtractedRowShape.table at h
  split_ifs at h <;>
    simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  all_goals first | contradiction | (rcases h with ⟨rfl, rfl⟩; decide)

theorem payload_length_mod (row : U8) (record payload : Slice U8)
    (h : AspisR1RecordParser.r1_wire.parse_record row record =
      ok (core.result.Result.Ok payload)) : payload.val.length % 32 = 0 := by
  obtain ⟨tag, size, b1, b2, b3, b4, ht, _, _, _, _, _, _, _, _, hp, _⟩ :=
    ExtractedRecordFraming.parse_record_success row record payload h
  rw [hp]
  exact table_size_mod row tag size ht

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

theorem successful_payload_covered (row : U8) (record payload : Slice U8)
    (h : AspisR1RecordParser.r1_wire.parse_record row record =
      ok (core.result.Result.Ok payload)) :
    (List.toChunksExact 32 (by decide) payload.val).2 = [] ∧
      (List.toChunksExact 32 (by decide) payload.val).1.flatten = payload.val :=
  chunks_cover_of_mod_zero 32 (by decide) payload.val (payload_length_mod row record payload h)

#print axioms table_size_mod
#print axioms payload_length_mod
#print axioms chunks_partition
#print axioms chunks_remainder_length
#print axioms chunks_full_length
#print axioms chunks_cover_of_mod_zero
#print axioms successful_payload_covered
end AspisR1.RecordPayloadPartition
