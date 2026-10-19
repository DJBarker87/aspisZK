import ExtractedRecordLimbCanonicality

/-!
Successful actual-F byte decoding: exact input length, eight LE4 words,
canonical limb bounds, and unchanged packing. No base-field, pointer,
validator-loop, or Rust refinement claim is made here.
-/
set_option autoImplicit false

namespace AspisR1.ExtractedRecordByteCanonicality
open Aeneas Aeneas.Std Result
open AspisR1RecordParser.field.wide_exact
open ExtractedRecordLimbCanonicality

/-- A bounded byte read; no default or out-of-bounds branch is used. -/
def byteAt (arr : Array U8 32#usize) (i : Fin 32) : U8 :=
  arr.val[i.val]'(by have := arr.property; change arr.val.length = 32 at this; omega)

/-- The same primitive little-endian U32 decoder called by actual-F. -/
def wordLE (arr : Array U8 32#usize) (i : Fin 8) : U32 :=
  core.num.U32.from_le_bytes (Array.make 4#usize
    [byteAt arr ⟨4 * i.val, by omega⟩,
     byteAt arr ⟨4 * i.val + 1, by omega⟩,
     byteAt arr ⟨4 * i.val + 2, by omega⟩,
     byteAt arr ⟨4 * i.val + 3, by omega⟩])

def wordArray8 (arr : Array U8 32#usize) : Array U32 8#usize :=
  Array.make 8#usize [wordLE arr 0, wordLE arr 1, wordLE arr 2, wordLE arr 3,
    wordLE arr 4, wordLE arr 5, wordLE arr 6, wordLE arr 7]

private theorem index_array32 (arr : Array U8 32#usize) (i : Usize)
    (hi : i.val < 32) :
    Slice.index_usize (Array.to_slice arr) i =
      ok (arr.val[i.val]'(by have := arr.property; change arr.val.length = 32 at this; omega)) := by
  have hb : i.val < arr.val.length := by
    have := arr.property
    change arr.val.length = 32 at this
    omega
  obtain ⟨x, hx, hval⟩ := WP.spec_imp_exists
    (Slice.index_usize_spec (Array.to_slice arr) i (by simpa [Array.to_slice] using hb))
  simpa [Array.to_slice] using hx.trans (congrArg Result.ok hval)

theorem wrong_length (bytes : Slice U8) (h : bytes.val.length ≠ 32) :
    WideExact.from_le_bytes bytes = ok none := by
  have hlen : Slice.len bytes ≠ 32#usize := by
    intro heq
    apply h
    have hv := congrArg UScalar.val heq
    simpa [Slice.len, Slice.length] using hv
  simp [WideExact.from_le_bytes, WideExact.BYTE_LEN, hlen]

/-- The 32 actual byte reads reduce to eight calls of the existing decoder. -/
theorem fixed_reads (arr : Array U8 32#usize) :
    WideExact.from_le_bytes (Array.to_slice arr) =
      WideExact.from_limbs (wordArray8 arr) := by
  have hlen : Slice.len (Array.to_slice arr) = 32#usize := by
    apply UScalar.eq_of_val_eq
    simp [Slice.len, Slice.length, Array.to_slice, arr.property]
  simp [WideExact.from_le_bytes, WideExact.BYTE_LEN, hlen,
    index_array32, wordArray8, wordLE, byteAt, lift]

theorem fixed_success_iff (arr : Array U8 32#usize) (w : WideExact) :
    WideExact.from_le_bytes (Array.to_slice arr) = ok (some w) ↔
      (∀ i : Fin 8, (wordLE arr i).val < 2147483647) ∧
      w = packed (wordLE arr 0) (wordLE arr 1) (wordLE arr 2) (wordLE arr 3)
        (wordLE arr 4) (wordLE arr 5) (wordLE arr 6) (wordLE arr 7) := by
  rw [fixed_reads, wordArray8, from_limbs_make_success_iff]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    Fin.forall_fin_succ, Fin.forall_fin_zero, and_true]

/-- Successful input has precisely the represented 32 bytes and eight
canonical decoded words; the returned value is their exact packing. -/
theorem slice_success (bytes : Slice U8) (w : WideExact)
    (h : WideExact.from_le_bytes bytes = ok (some w)) :
    bytes.val.length = 32 ∧
      ∃ arr : Array U8 32#usize, Array.to_slice arr = bytes ∧
        (∀ i : Fin 8, (wordLE arr i).val < 2147483647) ∧
        w = packed (wordLE arr 0) (wordLE arr 1) (wordLE arr 2) (wordLE arr 3)
          (wordLE arr 4) (wordLE arr 5) (wordLE arr 6) (wordLE arr 7) := by
  have hlen : bytes.val.length = 32 := by
    by_contra hn
    rw [wrong_length bytes hn] at h
    cases h
  let arr : Array U8 32#usize := ⟨bytes.val, by simpa using hlen⟩
  have hs : Array.to_slice arr = bytes := by cases bytes; rfl
  refine ⟨hlen, arr, hs, ?_⟩
  apply (fixed_success_iff arr w).mp
  simpa only [hs] using h

end AspisR1.ExtractedRecordByteCanonicality

#print axioms AspisR1.ExtractedRecordByteCanonicality.wrong_length
#print axioms AspisR1.ExtractedRecordByteCanonicality.fixed_reads
#print axioms AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff
#print axioms AspisR1.ExtractedRecordByteCanonicality.slice_success
