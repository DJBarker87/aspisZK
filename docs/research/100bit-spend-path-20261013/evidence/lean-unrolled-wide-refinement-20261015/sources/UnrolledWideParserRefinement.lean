import UnrolledWideByteReads
import R1UnrolledWideLimbChecks
import R1CandidateWideParserContracts

/-! All-input refinement of the retained h2 parser to the existing strict
wide-byte decoder. The argument reuses the earlier byte, word, and canonical
decoder theorems; no successful-parse or canonical-input premise is assumed. -/
set_option autoImplicit false

namespace AspisR1.UnrolledWideParserRefinement

open Aeneas Aeneas.Std Result
open AspisR1.RetainedFieldByteCodec
open AspisR1.StrictWideByteCodec
open AspisR1.WideParserArrayHalves
open AspisR1.AeneasWordCodec
open AspisR1.UnrolledWideByteReads
open AspisR1.CandidateWideParserRefinement (Wide limbsToCandidate)

private theorem word_guard (bytes : WordBytes) :
    (aeneasWord bytes ≥ AspisR1CandidateParser.field.P) ↔
      ¬ (decodeWordLE bytes).val < m31Modulus := by
  change AspisR1CandidateParser.field.P.val ≤ (aeneasWord bytes).val ↔ _
  rw [aeneasWord_val_eq]
  have hp : AspisR1CandidateParser.field.P.val = m31Modulus := by
    norm_num [AspisR1CandidateParser.field.P, m31Modulus, rawCandidateCount]
  rw [hp]
  omega

private theorem canonical_word (bytes : WordBytes)
    (h : (decodeWordLE bytes).val < m31Modulus) :
    aeneasWord bytes = AspisR1.M31ParserRefinement.valueToU32
      ⟨(decodeWordLE bytes).val, h⟩ := by
  apply UScalar.eq_of_val_eq
  rw [aeneasWord_val_eq, AspisR1.M31ParserRefinement.valueToU32_val]

theorem limbs_refine (bytes : WideBytes) :
    AspisR1CandidateParser.field.wide_exact.WideExact.from_limbs_unrolled
        (wordArray8 bytes) =
      Result.ok ((decodeWideLE bytes).map limbsToCandidate) := by
  have hguards :
      (lowWord bytes 0 ≥ AspisR1CandidateParser.field.P ∨
       lowWord bytes 1 ≥ AspisR1CandidateParser.field.P ∨
       lowWord bytes 2 ≥ AspisR1CandidateParser.field.P ∨
       lowWord bytes 3 ≥ AspisR1CandidateParser.field.P ∨
       highWord bytes 0 ≥ AspisR1CandidateParser.field.P ∨
       highWord bytes 1 ≥ AspisR1CandidateParser.field.P ∨
       highWord bytes 2 ≥ AspisR1CandidateParser.field.P ∨
       highWord bytes 3 ≥ AspisR1CandidateParser.field.P) ↔
      ¬ ((∀ i, (decodeWordLE (qm31LimbBytes (lowBytes bytes) i)).val < m31Modulus) ∧
         (∀ i, (decodeWordLE (qm31LimbBytes (highBytes bytes) i)).val < m31Modulus)) := by
    simp only [lowWord, highWord, word_guard]
    simp only [Fin.forall_fin_succ, Fin.forall_fin_zero, and_true,
      not_and_or, or_assoc]
    rfl
  rw [wordArray8, AspisR1.UnrolledWideLimbChecks.from_limbs_make]
  simp only [hguards]
  by_cases hlo : ∀ i, (decodeWordLE (qm31LimbBytes (lowBytes bytes) i)).val < m31Modulus
  · by_cases hhi : ∀ i, (decodeWordLE (qm31LimbBytes (highBytes bytes) i)).val < m31Modulus
    · simp only [lowWord, highWord]
      rw [canonical_word _ (hlo 0), canonical_word _ (hlo 1),
        canonical_word _ (hlo 2), canonical_word _ (hlo 3),
        canonical_word _ (hhi 0), canonical_word _ (hhi 1),
        canonical_word _ (hhi 2), canonical_word _ (hhi 3)]
      simp [decodeWideLE, decodeQM31LE, hlo, hhi, limbsToCandidate,
        AspisR1.CandidateStrictQM31Parser.limbsToCandidate]
    · simp [decodeWideLE, decodeQM31LE, hlo, hhi]
  · simp [decodeWideLE, decodeQM31LE, hlo]

theorem source_refines (arr : Array U8 32#usize) :
    AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled
        (Array.to_slice arr) =
      Result.ok ((decodeWideLE (arrayBytes32 arr)).map limbsToCandidate) := by
  rw [fixed_reads, limbs_refine]

theorem source_eq_half_parser (bytes : Slice U8) :
    AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled bytes =
      AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes bytes := by
  by_cases hlen : bytes.val.length = 32
  · let arr : Array U8 32#usize := ⟨bytes.val, by simpa using hlen⟩
    have hs : Array.to_slice arr = bytes := by cases bytes; rfl
    rw [← hs, source_refines, AspisR1.CandidateWideParserRefinement.source_refines]
  · rw [wrong_length bytes hlen,
      AspisR1.CandidateWideParserRefinement.wrong_length bytes hlen]

theorem total (bytes : Slice U8) :
    ∃ out : Option Wide,
      AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled bytes =
        Result.ok out := by
  rw [source_eq_half_parser]
  exact AspisR1.CandidateWideParserContracts.total bytes

theorem slice_success_canonical (bytes : Slice U8) (value : Wide)
    (h : AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled
      bytes = Result.ok (some value)) :
    bytes.val.length = 32 ∧
      AspisR1.CandidateFieldCanonicality.qmCanonical value.c0 ∧
      AspisR1.CandidateFieldCanonicality.qmCanonical value.c1 := by
  rw [source_eq_half_parser] at h
  exact AspisR1.CandidateWideParserContracts.slice_success_canonical bytes value h

theorem fixed_success (arr : Array U8 32#usize) (value : Wide)
    (h : AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled
      (Array.to_slice arr) = Result.ok (some value)) :
    ∃ limbs : WideLimbs,
      decodeWideLE (arrayBytes32 arr) = some limbs ∧
      limbsToCandidate limbs = value ∧
      encodeWideLE limbs = arrayBytes32 arr := by
  rw [source_eq_half_parser] at h
  exact AspisR1.CandidateWideParserContracts.fixed_success arr value h

#print axioms limbs_refine
#print axioms source_refines
#print axioms source_eq_half_parser
#print axioms total
#print axioms slice_success_canonical
#print axioms fixed_success

end AspisR1.UnrolledWideParserRefinement
