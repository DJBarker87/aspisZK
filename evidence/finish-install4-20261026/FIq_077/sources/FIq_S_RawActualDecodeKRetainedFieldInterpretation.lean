import FIq_S_RawActualDecodeKMainStrictReadback
import FIq_S_R1SourceWideExactCodec

set_option autoImplicit false
namespace AspisR1PublicPreparation.RawActualDecodeKRetainedFieldInterpretation
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter
open AspisR1PublicPreparation.RawActualDecodeKMainAdapter
open AspisR1PublicPreparation.RawActualDecodeKMainStrictReadback
open AspisR1.ActualDecodeKStrictQM31Parser
open AspisR1.RetainedFieldByteCodec

/-- Reuse the retained canonical-limb field interpretation. All intermediate
record adapters preserve the four original machine coordinates literally. -/
theorem limbsToActual_field (limbs : QM31Limbs) :
    AspisR1.ExtractedMaskQM31Exact.decode
      (mainToProbe (decoderQMToMain (limbsToActual limbs))) =
      AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv limbs := by
  change AspisR1.SourceWideExactCodec.candidateQMToExact
    (AspisR1.CandidateStrictQM31Parser.limbsToCandidate limbs) = _
  exact AspisR1.SourceWideExactCodec.candidateQMToExact_limbsToCandidate limbs

/-- Every actual Main coefficient has the exact retained field interpretation
of the canonical limbs decoded from its original indexed byte reads. -/
theorem decodeMain_success_exact_field
    (n : Usize) (r : MainRecord) (offset : Usize) (out : Array MainQM n)
    (h : decodeMain n r offset = .ok (.Ok out)) :
    ∃ byteOffset : Usize,
      lift (Usize.checked_mul offset 32#usize) = .ok (some byteOffset) ∧
      ∀ j : Fin n, ∃ q : DecodeQM,
        ∃ trace : Trace (recordToDecoder r) byteOffset
          (UScalar.ofNatCore j.val (by have := j.isLt; scalar_tac)) offset q,
        ∃ limbs : QM31Limbs,
          decodeQM31LE (AspisR1.CandidateParserByteOrder.arrayBytes16 (inputArray trace)) = some limbs ∧
          encodeQM31LE limbs = AspisR1.CandidateParserByteOrder.arrayBytes16 (inputArray trace) ∧
          AspisR1.ExtractedMaskQM31Exact.decode
            (mainToProbe (out.val[j.val]'(by simpa [out.property] using j.isLt))) =
              AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv limbs := by
  obtain ⟨byteOffset,hOffset,hvalues⟩ := decodeMain_success_strict_readback n r offset out h
  refine ⟨byteOffset,hOffset,?_⟩
  intro j
  obtain ⟨q,trace,limbs,_hcall,hcell,hdecode,hencode⟩ := hvalues j
  refine ⟨q,trace,limbs,hdecode,hencode,?_⟩
  rw [hcell]
  exact limbsToActual_field limbs

#print axioms limbsToActual_field
#print axioms decodeMain_success_exact_field
end AspisR1PublicPreparation.RawActualDecodeKRetainedFieldInterpretation
