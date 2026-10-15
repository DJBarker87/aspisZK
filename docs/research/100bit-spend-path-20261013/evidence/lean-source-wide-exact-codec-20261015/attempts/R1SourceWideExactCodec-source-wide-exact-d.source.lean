import R1FoldedLeafCodec
import UnrolledWideParserRefinement

/-! Coordinate interpretation of the extracted candidate WideExact structure
into the retained exact tower, and its successful-parse byte-codec bridge.
This is representation plumbing only; it proves no source arithmetic fact. -/
set_option autoImplicit false

namespace AspisR1.SourceWideExactCodec

open Aeneas Aeneas.Std Result
open AspisR1.RetainedFieldByteCodec
open AspisR1.StrictWideByteCodec
open AspisR1.WideExactLimbCodec
open AspisV8R15.ExactTowerBase
open AspisWideTower

abbrev CandidateQM := AspisR1CandidateParser.field.QM31
abbrev CandidateWide := AspisR1CandidateParser.field.wide_exact.WideExact
abbrev WideLimbs := AspisR1.StrictWideByteCodec.WideLimbs
abbrev Wide := AspisWideTower.WideExact

def candidateQMToExact (v : CandidateQM) : QM31Exact :=
  ⟨⟨(v.c0.a.val : M31Exact), (v.c0.b.val : M31Exact)⟩,
   ⟨(v.c1.a.val : M31Exact), (v.c1.b.val : M31Exact)⟩⟩

def candidateWideToExact (v : CandidateWide) : Wide :=
  ⟨candidateQMToExact v.c0, candidateQMToExact v.c1⟩

private theorem residueEquiv_natCast (x : M31Value) :
    AspisR1.RetainedExactLimbCodec.m31ResidueEquiv x = (x.val : M31Exact) := by
  apply ZMod.val_injective P
  change x.val = (x.val : ZMod P).val
  rw [ZMod.val_natCast_of_lt x.isLt]

theorem candidateQMToExact_limbsToCandidate (limbs : QM31Limbs) :
    candidateQMToExact
      (AspisR1.CandidateStrictQM31Parser.limbsToCandidate limbs) =
        AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv limbs := by
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext <;>
      simp [candidateQMToExact,
        AspisR1.CandidateStrictQM31Parser.limbsToCandidate,
        AspisR1.M31ParserRefinement.valueToU32_val,
        AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv,
        AspisR1.RetainedExactLimbCodec.limbsToQM31Exact,
        residueEquiv_natCast]
  · apply QuadraticAlgebra.ext <;>
      simp [candidateQMToExact,
        AspisR1.CandidateStrictQM31Parser.limbsToCandidate,
        AspisR1.M31ParserRefinement.valueToU32_val,
        AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv,
        AspisR1.RetainedExactLimbCodec.limbsToQM31Exact,
        residueEquiv_natCast]

theorem candidateWideToExact_limbsToCandidate (limbs : WideLimbs) :
    candidateWideToExact
      (AspisR1.CandidateWideParserRefinement.limbsToCandidate limbs) =
        pairExactEquiv limbs := by
  rw [pairExactEquiv_apply]
  cases limbs with
  | mk lo hi =>
      apply QuadraticAlgebra.ext
      · simpa [candidateWideToExact,
          AspisR1.CandidateWideParserRefinement.limbsToCandidate,
          pairToExact] using candidateQMToExact_limbsToCandidate lo
      · simpa [candidateWideToExact,
          AspisR1.CandidateWideParserRefinement.limbsToCandidate,
          pairToExact] using candidateQMToExact_limbsToCandidate hi

theorem successful_parse_decodes (arr : Array U8 32#usize)
    (value : CandidateWide)
    (h : AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled
      (Array.to_slice arr) = Result.ok (some value)) :
    AspisR1.FoldedLeafCodec.decodeWide
      (List.ofFn (AspisR1.WideParserArrayHalves.arrayBytes32 arr)) =
        some (candidateWideToExact value) := by
  obtain ⟨limbs, hdecode, hvalue, _hbytes⟩ :=
    AspisR1.UnrolledWideParserRefinement.fixed_success arr value h
  have hinterpret := congrArg candidateWideToExact hvalue
  have hdecoded : AspisR1.FoldedLeafCodec.decodeWide
      (List.ofFn (AspisR1.WideParserArrayHalves.arrayBytes32 arr)) =
        some (pairExactEquiv limbs) := by
    unfold AspisR1.FoldedLeafCodec.decodeWide
    rw [AspisR1.ListFieldCodec.fixedBytes?_ofFn]
    simp [hdecode]
  calc
    AspisR1.FoldedLeafCodec.decodeWide
        (List.ofFn (AspisR1.WideParserArrayHalves.arrayBytes32 arr)) =
        some (pairExactEquiv limbs) := hdecoded
    _ = some (candidateWideToExact value) := congrArg some <| by
      calc
        pairExactEquiv limbs = candidateWideToExact
            (AspisR1.CandidateWideParserRefinement.limbsToCandidate limbs) :=
          (candidateWideToExact_limbsToCandidate limbs).symm
        _ = candidateWideToExact value := hinterpret

#print axioms candidateQMToExact_limbsToCandidate
#print axioms candidateWideToExact_limbsToCandidate
#print axioms successful_parse_decodes

end AspisR1.SourceWideExactCodec
