import NDF_ChunkWords
import ExtractedRecordHighZero
set_option autoImplicit false
namespace NDF_ChunkCodec
open Aeneas Aeneas.Std Result
open AspisR1.ExtractedRecordByteCanonicality AspisR1.ExtractedRecordLimbCanonicality
open AspisR1.ExtractedRecordHighZero AspisR1RecordParser.field

theorem good_iff (arr : Array U8 32#usize) :
    NDF_ChunkWords.Good arr ↔ ∃ w,
      wide_exact.WideExact.from_le_bytes (Array.to_slice arr)=ok (some w) ∧ w.c1=QM31.ZERO := by
  constructor
  · intro good
    let w := packed (wordLE arr 0) (wordLE arr 1) (wordLE arr 2) (wordLE arr 3)
      (wordLE arr 4) (wordLE arr 5) (wordLE arr 6) (wordLE arr 7)
    have zero (i : Fin 8) (high : 4≤i.val) : wordLE arr i=0#u32 := by
      apply UScalar.eq_of_val_eq
      have h := (good i).2
      have hzero : (wordLE arr i).val=0 := h.resolve_left (by omega)
      simpa using hzero
    refine ⟨w,(fixed_success_iff arr w).mpr ⟨fun i => (good i).1,rfl⟩,?_⟩
    simp [w,packed,zero 4 (by decide),zero 5 (by decide),zero 6 (by decide),zero 7 (by decide),QM31.ZERO]
  · rintro ⟨w,decoded,high⟩
    obtain ⟨canonical,same⟩ := (fixed_success_iff arr w).mp decoded
    subst w
    have words := (qm31_eq_zero_iff _).mp high
    intro i
    refine ⟨canonical i,?_⟩
    by_cases low : i.val<4
    · exact Or.inl low
    · right
      fin_cases i <;> simp_all [packed]

theorem valid_iff (arr : Array U8 32#usize) :
    LPl_Kit_Bytes.validChunk 8 true arr.val=true ↔ ∃ w,
      wide_exact.WideExact.from_le_bytes (Array.to_slice arr)=ok (some w) ∧ w.c1=QM31.ZERO := by
  rw [NDF_ChunkWords.valid_iff,good_iff]

#print axioms good_iff
#print axioms valid_iff
end NDF_ChunkCodec
