import PreparedPost25TranscriptTransport
import GammaCandidateScalarTranscriptFieldRank

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1PublicPreparation.Post25GammaCallerAdapter

open AspisR1PublicPreparation.Post25TranscriptTransport

/-- A successful current scalar call with its gamma/ordinary callbacks supplied by the
candidate sampler, transported back through the explicit WideExact field map, yields
exactly the candidate row-27 scalar success package.  The other Prepared boundaries are
preserved and remain available to the caller. -/
theorem prepared_gamma_scalar_success_fieldRank {H : Type}
    (B : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (D : CurrentDigest H) (self after : CurrentTranscript H)
    (payload : Slice U8) (out : CurrentWide)
    (h : AspisR1PublicPreparation.PreparedModel.scalar
      (withCandidateScalars B AspisR1Post25Transcript.GammaCandidateSourceModel.gammaCandidateOps)
      D self 27#u8 payload true = .ok (out, after)) :
    ∃ block absorbed nextState,
      (digestToCandidate D).digest (transcriptToCandidate self).hash
        (AspisR1Post25Transcript.TranscriptSuccess.absorbParts
          (transcriptToCandidate self).state 187#u8 payload) = .ok absorbed ∧
      (digestToCandidate D).digest (transcriptToCandidate self).hash
        (AspisR1Post25Transcript.TranscriptSuccess.readParts absorbed 1#u8) = .ok block ∧
      (digestToCandidate D).digest (transcriptToCandidate self).hash
        (AspisR1Post25Transcript.TranscriptSuccess.readParts absorbed 2#u8) = .ok nextState ∧
      transcriptToCandidate after =
        {transcriptToCandidate self with state := nextState} ∧
      AspisR1Post25Transcript.OrdinaryCandidateSourceModel.decode
        (wideToCandidate out) =
        R0C.ModuloField.fieldRank ⟨
          AspisR1.SourceSamplerByteRank.rank block %
            (AspisR1.SamplerMachineBounds.P ^ 8 - 1) + 1, by
          have hb := (AspisR1.SamplerNatModel.gammaDigits_value_bounds
            (AspisR1.SourceSamplerByteRank.rank_lt block)).2
          rw [AspisR1.SamplerNatModel.gammaDigits_value
            (AspisR1.SourceSamplerByteRank.rank_lt block)] at hb
          simpa [AspisR1.SamplerMachineBounds.P,
            AspisCircleGroupOrder.P] using hb⟩ := by
  have hc := scalar_success_candidate_ops B
    AspisR1Post25Transcript.GammaCandidateSourceModel.gammaCandidateOps
    D self 27#u8 payload true out after h
  obtain ⟨block, absorbed, nextState, sample, digits, habs, hread, hstate,
      hafter, _hgamma, _hcanonical, _hscalar, hfield⟩ :=
    AspisR1Post25Transcript.GammaCandidateSourceModel.scalar_true_success_fieldRank
      (digestToCandidate D) (transcriptToCandidate self) (transcriptToCandidate after)
      payload (wideToCandidate out) hc
  exact ⟨block, absorbed, nextState, habs, hread, hstate, hafter, hfield⟩

#print axioms prepared_gamma_scalar_success_fieldRank

end AspisR1PublicPreparation.Post25GammaCallerAdapter
