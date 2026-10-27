import RPz7_PSem_SemanticRows
set_option autoImplicit false
noncomputable section
namespace AspisR1.PAln_RowBounds
open AspisV8R19.DuplexFrames OraclePortCompactDraft

theorem shape_bound (row : Nat) : 5+(rowShape row).2≤3717 := by
  unfold rowShape
  split_ifs <;> omega

theorem rows_bound (row : Nat) (rs : List Bytes) (h : PSem_Lengths.Rows row rs) :
    ∀ b ∈ rs, b.length≤3717 := by
  induction h with
  | nil => simp
  | @cons row b bs size tail ih =>
    intro x member
    rcases List.mem_cons.mp member with rfl | member
    · rw [size]; exact shape_bound row
    · exact ih x member

theorem semantic_bound (fuel row : Nat) (b : Bytes) (rs : List Bytes)
    (h : semanticRows fuel row b=some rs) : ∀ frame ∈ rs, frame.length≤3717 :=
  rows_bound row rs (PSem_Lengths.expanded_lengths fuel row b rs
    ((PSem_Rows.strict_iff fuel row b rs).mp h).2)

theorem slice_length (b : Bytes) (offset n : Nat) (h : offset+n≤b.length) :
    (slice b offset n).length=n := by
  simp only [slice,List.length_take,List.length_drop]
  omega

theorem le32_length (n : Nat) : (le32 n).length=4 := by
  simp only [le32,List.length_map,List.length_range]

theorem framed_length (b : Bytes) : (framed b).length=4+b.length := by
  simp only [framed,List.length_append,le32_length]

theorem row_bound (p : Parsed)
    (rows : semanticRows 27 0 (slice p.wire 48 6983)=some p.semantic)
    (length : p.wire.length=57607) (row : Nat) :
    (rowBytes p row).length≤3717 := by
  have sem := semantic_bound 27 0 _ _ rows
  have y1 : (expand 29 (slice p.wire 7031 464)).length=928 := by
    apply PSem_Expand.expand_length
    exact slice_length p.wire 7031 464 (by omega)
  unfold rowBytes
  split
  · cases h : p.semantic[row]? with
    | none => simp
    | some frame =>
      exact sem frame (List.mem_of_getElem? h)
  · split_ifs <;> simp only [framed_length]
    · rw [y1]; omega
    · rw [slice_length _ _ _ (by omega)]; omega
    · rw [slice_length _ _ _ (by omega)]; omega
    · rw [slice_length _ _ _ (by omega)]; omega
    · rw [slice_length _ _ _ (by omega)]; omega
    · simp

#print axioms shape_bound
#print axioms rows_bound
#print axioms semantic_bound
#print axioms slice_length
#print axioms le32_length
#print axioms framed_length
#print axioms row_bound
end AspisR1.PAln_RowBounds
end
