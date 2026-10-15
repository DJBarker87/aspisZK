import R1CandidateWideParserRefinement
import R1CandidateFieldCanonicality

/-! Totality, successful-decode shape, and limb canonicality contracts for the
   retained candidate WideExact parser. These are parser-model facts only. -/
set_option autoImplicit false

namespace AspisR1.CandidateWideParserContracts

open Aeneas Aeneas.Std Result
open AspisR1.RetainedFieldByteCodec
open AspisR1.StrictWideByteCodec
open AspisR1.WideParserArrayHalves
open AspisR1.CandidateWideParserRefinement

abbrev Wide := AspisR1.CandidateWideParserRefinement.Wide

theorem total (bytes : Slice U8) :
    ∃ out : Option Wide,
      AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes bytes =
        Result.ok out := by
  by_cases hlen : bytes.val.length = 32
  · let arr : Array U8 32#usize := ⟨bytes.val, by simpa using hlen⟩
    have hs : Array.to_slice arr = bytes := by
      cases bytes
      rfl
    refine ⟨(decodeWideLE (arrayBytes32 arr)).map limbsToCandidate, ?_⟩
    rw [← hs]
    exact source_refines arr
  · exact ⟨none, wrong_length bytes hlen⟩

theorem fixed_success (arr : Array U8 32#usize)
    (value : Wide)
    (h : AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes
      (Array.to_slice arr) = Result.ok (some value)) :
    ∃ limbs : WideLimbs,
      decodeWideLE (arrayBytes32 arr) = some limbs ∧
      limbsToCandidate limbs = value ∧
      encodeWideLE limbs = arrayBytes32 arr := by
  have hmap : (decodeWideLE (arrayBytes32 arr)).map limbsToCandidate =
      some value := by
    rw [source_refines] at h
    exact Result.ok.inj h
  cases hd : decodeWideLE (arrayBytes32 arr) with
  | none => simp [hd] at hmap
  | some limbs =>
      have hv : limbsToCandidate limbs = value := by
        simpa [hd] using hmap
      exact ⟨limbs, hd, hv,
        encodeWideLE_of_decodeWideLE _ _ hd⟩

theorem slice_success_canonical (bytes : Slice U8)
    (value : Wide)
    (h : AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes
      bytes = Result.ok (some value)) :
    bytes.val.length = 32 ∧
      AspisR1.CandidateFieldCanonicality.qmCanonical value.c0 ∧
      AspisR1.CandidateFieldCanonicality.qmCanonical value.c1 := by
  obtain ⟨out, hout⟩ := total bytes
  have houtval : out = some value := Result.ok.inj (hout.symm.trans h)
  have hlen : bytes.val.length = 32 := by
    by_contra hne
    have := wrong_length bytes hne
    rw [h] at this
    cases houtval
    simp at this
  let arr : Array U8 32#usize := ⟨bytes.val, by simpa using hlen⟩
  have hs : Array.to_slice arr = bytes := by
    cases bytes
    rfl
  have harr : AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes
      (Array.to_slice arr) = Result.ok (some value) := by
    simpa [hs] using h
  obtain ⟨limbs, hdecode, hv, _hencode⟩ := fixed_success arr value harr
  obtain ⟨hlo, hhi⟩ := successful_halves (arrayBytes32 arr) limbs hdecode
  have hc0 : AspisR1.CandidateStrictQM31Parser.limbsToCandidate limbs.1 =
      value.c0 := by
    have := congrArg (fun w : Wide => w.c0) hv
    simpa [limbsToCandidate] using this
  have hc1 : AspisR1.CandidateStrictQM31Parser.limbsToCandidate limbs.2 =
      value.c1 := by
    have := congrArg (fun w : Wide => w.c1) hv
    simpa [limbsToCandidate] using this
  have hsrc0 := AspisR1.CandidateStrictQM31Parser.source_refines (half0 arr)
  rw [half0_bytes] at hsrc0
  have hsrc1 := AspisR1.CandidateStrictQM31Parser.source_refines (half1 arr)
  rw [half1_bytes] at hsrc1
  have hqm0 : AspisR1CandidateParser.field.QM31.from_le_bytes
      (Array.to_slice (half0 arr)) = Result.ok (some value.c0) := by
    rw [hsrc0, hlo]
    exact congrArg (fun x => Result.ok (some x)) hc0
  have hqm1 : AspisR1CandidateParser.field.QM31.from_le_bytes
      (Array.to_slice (half1 arr)) = Result.ok (some value.c1) := by
    rw [hsrc1, hhi]
    exact congrArg (fun x => Result.ok (some x)) hc1
  refine ⟨hlen, ?_, ?_⟩
  · exact AspisR1.CandidateFieldCanonicality.source_qm31_success_canonical
      (half0 arr) value.c0 hqm0
  · exact AspisR1.CandidateFieldCanonicality.source_qm31_success_canonical
      (half1 arr) value.c1 hqm1

#print axioms total
#print axioms fixed_success
#print axioms slice_success_canonical

end AspisR1.CandidateWideParserContracts
