import OraclePortCompactDraft

/-! Frozen Fiat–Shamir row projection cannot recover the opening/node suffix.
The total row capacity is not the size of the actual absorbed messages. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortRowStorageC4
open AspisV8R19.DuplexFrames
open OraclePortCompactDraft

theorem slice_prefix (headBytes tail : Bytes) (offset size : Nat)
    (bound : offset + size ≤ headBytes.length) :
    slice (headBytes ++ tail) offset size = slice headBytes offset size := by
  unfold slice
  rw [List.drop_append_of_le_length (by omega)]
  exact List.take_append_of_le_length (by simp only [List.length_drop]; omega)

/-- All physical slices used by rowBytes end at or before OFF_OPENINGS.
semantic is the separately expanded, parsed semantic headBytes. -/
theorem rows_ignore_suffix (headBytes left right : Bytes) (semantic : List Bytes)
    (length : headBytes.length = 10055) (row : Nat) :
    rowBytes ⟨headBytes ++ left,semantic⟩ row =
      rowBytes ⟨headBytes ++ right,semantic⟩ row := by
  have hs (offset size : Nat) (h : offset + size ≤ 10055) :
      slice (headBytes ++ left) offset size = slice (headBytes ++ right) offset size := by
    rw [slice_prefix headBytes left offset size (by omega),
      slice_prefix headBytes right offset size (by omega)]
  unfold rowBytes
  dsimp only
  split
  · rfl
  · split
    · rw [hs 7031 464 (by decide)]
    · split
      · rw [hs 7495 32 (by decide)]
      · split
        · rw [hs 7527 224 (by decide)]
        · split
          · rw [hs 7751 256 (by decide)]
          · split
            · rw [hs 8007 2048 (by decide)]
            · rfl

/-- Two exact-length stored carriers with identical absorbed rows, but a
changed first opening byte. This is a projection counterexample, not a
claim that either carrier is an accepted proof. -/
theorem exact_length_ambiguity (headBytes : Bytes) (semantic : List Bytes)
    (length : headBytes.length = 10055) :
    ∃ left right : Parsed,
      left.wire.length = 57607 ∧ right.wire.length = 57607 ∧
      (∀ row, rowBytes left row = rowBytes right row) ∧
      slice left.wire 10055 1 ≠ slice right.wire 10055 1 := by
  let zeros : Bytes := List.replicate 47551 0
  refine ⟨⟨headBytes ++ (0 :: zeros),semantic⟩,
    ⟨headBytes ++ (1 :: zeros),semantic⟩, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_append,List.length_cons,List.length_replicate,zeros,length]
  · simp only [List.length_append,List.length_cons,List.length_replicate,zeros,length]
  · exact rows_ignore_suffix headBytes _ _ semantic length
  · simp only [slice, ← length, List.drop_append_length, List.take_succ_cons,
      List.take_zero, ne_eq,List.cons.injEq, and_true]
    decide

#print axioms slice_prefix
#print axioms rows_ignore_suffix
#print axioms exact_length_ambiguity
end AspisR1.OraclePortRowStorageC4
end
