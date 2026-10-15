import UnrolledWideParserSource
import R1CandidateWideParserRefinement

/-! The unrolled parser's fixed byte reads, expressed through the previously
proved little-endian word codec. All byte arrays are allowed; canonicality is
checked by the downstream limb parser, not assumed here. -/
set_option autoImplicit false

namespace AspisR1.UnrolledWideByteReads

open Aeneas Aeneas.Std Result
open AspisR1.RetainedFieldByteCodec
open AspisR1.StrictWideByteCodec
open AspisR1.WideParserArrayHalves
open AspisR1.AeneasWordCodec

def lowWord (bytes : WideBytes) (i : Fin 4) : U32 :=
  aeneasWord (qm31LimbBytes (lowBytes bytes) i)

def highWord (bytes : WideBytes) (i : Fin 4) : U32 :=
  aeneasWord (qm31LimbBytes (highBytes bytes) i)

def wordArray8 (bytes : WideBytes) : Array U32 8#usize :=
  Array.make 8#usize
    [lowWord bytes 0, lowWord bytes 1, lowWord bytes 2, lowWord bytes 3,
     highWord bytes 0, highWord bytes 1, highWord bytes 2, highWord bytes 3]

theorem index_array32 (arr : Array U8 32#usize) (i : Usize) (hi : i.val < 32) :
    Slice.index_usize (Array.to_slice arr) i =
      Result.ok (arr.val[i.val]'(by have := arr.property; change arr.val.length = 32 at this; omega)) := by
  have hb : i.val < arr.val.length := by
    have := arr.property
    change arr.val.length = 32 at this
    omega
  obtain ⟨x, hx, hval⟩ := WP.spec_imp_exists
    (Slice.index_usize_spec (Array.to_slice arr) i (by simpa [Array.to_slice] using hb))
  simpa [Array.to_slice] using hx.trans (congrArg Result.ok hval)

theorem wrong_length (bytes : Slice U8) (h : bytes.val.length ≠ 32) :
    AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled bytes =
      Result.ok none := by
  have hlen : Slice.len bytes ≠ 32#usize := by
    intro heq
    apply h
    have hv := congrArg UScalar.val heq
    simpa [Slice.len, Slice.length] using hv
  simp [AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled,
    AspisR1CandidateParser.field.wide_exact.WideExact.BYTE_LEN, hlen]

theorem fixed_reads (arr : Array U8 32#usize) :
    AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled
        (Array.to_slice arr) =
      AspisR1CandidateParser.field.wide_exact.WideExact.from_limbs_unrolled
        (wordArray8 (arrayBytes32 arr)) := by
  have hlen : Slice.len (Array.to_slice arr) = 32#usize := by
    apply UScalar.eq_of_val_eq
    simp [Slice.len, Slice.length, Array.to_slice, arr.property]
  simp [AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled,
    AspisR1CandidateParser.field.wide_exact.WideExact.BYTE_LEN, hlen,
    index_array32, wordArray8, lowWord, highWord, aeneasWord,
    qm31LimbBytes, lowBytes, highBytes, limbByteIndex, arrayBytes32,
    AspisV8R19.SqueezeOracleBridge.word_roundtrip, lift, finProdFinEquiv]

#print axioms index_array32
#print axioms wrong_length
#print axioms fixed_reads

end AspisR1.UnrolledWideByteReads
