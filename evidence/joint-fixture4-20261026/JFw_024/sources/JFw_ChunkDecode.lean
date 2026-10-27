import PSem_FieldCanonical
import ExtractedRecordValidator
set_option autoImplicit false
namespace AspisR1.JFw_ChunkDecode
open Aeneas Aeneas.Std Result
open AspisR1RecordParser ExtractedRecordValidator ExtractedRecordByteCanonicality
open ExtractedRecordLimbCanonicality ExtractedRecordStrictCodec ExtractedRecordHighZero
open OraclePortCompactDraft MultiproofConeCanonical

theorem high_word (arr : Array U8 32#usize) (zero : arr.val.drop 16 = List.replicate 16 0#u8)
    (j : Fin 8) (high : 4 ≤ j.val) : wordLE arr j = 0#u32 := by
  have offset : arr.val.drop (4*j.val) = (arr.val.drop 16).drop (4*j.val-16) := by
    rw [List.drop_drop]
    congr 1
    omega
  have sliceZero : slice (bytesOf arr.val) (4*j.val) 4 = List.replicate 4 0 := by
    simp only [slice,bytesOf,←List.map_drop,←List.map_take,offset,zero,
      List.drop_replicate,List.take_replicate,List.map_replicate]
    congr 1
    omega
  have h := PSem_FieldCanonical.word_slice arr j
  rw [sliceZero] at h
  have numeric := congrArg little h
  rw [PSem_Canonical.little_zeros,MultiproofConeEndian.little_four,decodeWord_at] at numeric
  apply UScalar.eq_of_val_eq
  exact numeric.symm

theorem valid (chunk : Slice U8) (length : chunk.val.length = 32)
    (canon : canonical (bytesOf chunk.val))
    (zero : chunk.val.drop 16 = List.replicate 16 0#u8) : ChunkValid chunk := by
  let arr : Array U8 32#usize := ⟨chunk.val,length⟩
  have same : Array.to_slice arr = chunk := by cases chunk;rfl
  have bounds : ∀ j : Fin 8,(wordLE arr j).val < 2147483647 := by
    intro j
    have hj : j.val ∈ List.range ((bytesOf arr.val).length/4) := by
      simp only [bytesOf,List.length_map,arr]
      rw [length]
      exact List.mem_range.mpr (by omega)
    have h := canon.2 j.val hj
    change little (slice (bytesOf arr.val) (4*j.val) 4) < _ at h
    rw [PSem_FieldCanonical.word_slice arr j,MultiproofConeEndian.little_four,decodeWord_at] at h
    exact h
  let w := packed (wordLE arr 0) (wordLE arr 1) (wordLE arr 2) (wordLE arr 3)
    (wordLE arr 4) (wordLE arr 5) (wordLE arr 6) (wordLE arr 7)
  refine ⟨w,?_,?_⟩
  · rw [←same]
    exact (fixed_success_iff arr w).mpr ⟨bounds,rfl⟩
  · apply (qm31_eq_zero_iff _).mpr
    exact ⟨high_word arr zero 4 (by decide),high_word arr zero 5 (by decide),
      high_word arr zero 6 (by decide),high_word arr zero 7 (by decide)⟩

#print axioms high_word
#print axioms valid
end AspisR1.JFw_ChunkDecode
