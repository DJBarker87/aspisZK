import OraclePortCheckpointAbiC5

/-! Symbolic field extraction from the physical checkpoint serializer. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortCheckpointSlicesC5
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCompactDraft OraclePortCheckpointAbiC5

/-- Work is structural in the list of fields, not in encoded field values. -/
theorem slice_index (bs : List Bytes) (i : Nat) (field : Bytes)
    (entry : bs[i]? = some field) :
    slice bs.flatten ((bs.take i).map List.length).sum field.length = field := by
  induction bs generalizing i with
  | nil => simp at entry
  | cons head rest ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at entry
      subst field
      simpa only [List.take_zero,List.map_nil,List.sum_nil,List.flatten_cons,List.nil_append,List.length_nil] using
        (OraclePortCheckpointAbiC5.slice_block [] head rest.flatten)
    | succ i =>
      simp only [List.getElem?_cons_succ] at entry
      simp only [List.take_succ_cons,List.map_cons,List.sum_cons,List.flatten_cons]
      unfold slice
      rw [← List.drop_drop,List.drop_append_length]
      exact ih i entry

theorem slice_prefix (head tail : Bytes) (offset size : Nat)
    (bound : offset + size ≤ head.length) :
    slice (head ++ tail) offset size = slice head offset size := by
  unfold slice
  rw [List.drop_append_of_le_length (by omega)]
  exact List.take_append_of_le_length (by simp only [List.length_drop]; omega)

/-- Fixed offsets are justified by the checked block-width table. -/
theorem field_at (H : Bytes → State) (stored pub : Bytes) (p : Prepared)
    (a : QueryAccumulator.State K E) (i offset width : Nat) (field : Bytes)
    (entry : (blocks p a (H stored) (H pub))[i]? = some field)
    (start : ((widths.take i).sum) = offset) (length : field.length = width)
    (bound : offset+width ≤ 1736) :
    slice (encode H stored pub p a) offset width = field := by
  have extracted := slice_index (blocks p a (H stored) (H pub)) i field entry
  rw [List.map_take,block_widths,start,length] at extracted
  change slice (body p a (H stored) (H pub)) offset width = field at extracted
  unfold encode
  rw [slice_prefix _ _ offset width (by rw [body_length]; exact bound)]
  exact extracted

theorem accumulator_slices (H : Bytes → State) (stored pub : Bytes) (p : Prepared)
    (a : QueryAccumulator.State K E) :
    slice (encode H stored pub p a) 664 32 = encodeE a.rhs ∧
    slice (encode H stored pub p a) 696 16 = encodeK a.power ∧
    slice (encode H stored pub p a) 712 1024 = encodeKs a.weights := by
  refine ⟨?_,?_,?_⟩
  · exact field_at H stored pub p a 15 664 32 _ rfl rfl (FoldedLeafCodec.encodeWide_length _) (by decide)
  · exact field_at H stored pub p a 16 696 16 _ rfl rfl (encodeK_length _) (by decide)
  · exact field_at H stored pub p a 17 712 1024 _ rfl rfl (encodeKs_length _) (by decide)

/-- Decoding the actual accumulator regions returns the written state. -/
theorem accumulator_decodes (H : Bytes → State) (stored pub : Bytes) (p : Prepared)
    (a : QueryAccumulator.State K E) :
    FoldedLeafCodec.decodeWide (slice (encode H stored pub p a) 664 32) = some a.rhs ∧
    ExactLeafFieldCodec.decodeQM31 (slice (encode H stored pub p a) 696 16) = some a.power ∧
    decodeKs 64 (slice (encode H stored pub p a) 712 1024) = some a.weights := by
  obtain ⟨rhs,power,weights⟩ := accumulator_slices H stored pub p a
  rw [rhs,power,weights]
  exact ⟨FoldedLeafCodec.decodeWide_encode _,ExactLeafFieldCodec.decodeQM31_encodeQM31 _,decodeKs_encode _⟩

theorem prepared_slices (H : Bytes → State) (stored pub : Bytes) (p : Prepared)
    (a : QueryAccumulator.State K E) :
    slice (encode H stored pub p a) 304 16 = encodeK p.rho ∧
    slice (encode H stored pub p a) 320 88 = queryBytes p.queries ∧
    slice (encode H stored pub p a) 408 160 = encodeKs p.semanticAlpha ∧
    slice (encode H stored pub p a) 568 64 = encodeKs p.coordinates ∧
    slice (encode H stored pub p a) 632 32 = encodeE p.claim := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact field_at H stored pub p a 10 304 16 _ rfl rfl (encodeK_length _) (by decide)
  · exact field_at H stored pub p a 11 320 88 _ rfl rfl (queryBytes_length _) (by decide)
  · exact field_at H stored pub p a 12 408 160 _ rfl rfl (encodeKs_length _) (by decide)
  · exact field_at H stored pub p a 13 568 64 _ rfl rfl (encodeKs_length _) (by decide)
  · exact field_at H stored pub p a 14 632 32 _ rfl rfl (FoldedLeafCodec.encodeWide_length _) (by decide)

#print axioms slice_index
#print axioms slice_prefix
#print axioms field_at
#print axioms accumulator_slices
#print axioms accumulator_decodes
#print axioms prepared_slices
end AspisR1.OraclePortCheckpointSlicesC5
end
