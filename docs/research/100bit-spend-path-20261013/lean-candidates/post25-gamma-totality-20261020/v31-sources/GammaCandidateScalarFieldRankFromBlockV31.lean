import GammaCandidateScalarTotalityV27

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1Post25Transcript.GammaCandidateSourceModel

open AspisR1GammaCaller.DigitsModel
open AspisR1Post25Transcript.OrdinaryCandidateSourceModel

theorem scalar_true_block_success_fieldRank {H : Type}
    (D : aspis_core.Digest32 H) (self after : transcript.Transcript H)
    (payload : Slice U8) (block : Bytes32)
    (hblock : transcript.Transcript.block D self 27#u8 payload = .ok (block, after)) :
    ∃ out : E,
      transcript.Transcript.scalar gammaCandidateOps D self 27#u8 payload true =
        .ok (out, after) ∧
      ∃ block' absorbed nextState sample digits,
        D.digest self.hash
          (TranscriptSuccess.absorbParts self.state 187#u8 payload) = .ok absorbed ∧
        D.digest self.hash (TranscriptSuccess.readParts absorbed 1#u8) = .ok block' ∧
        D.digest self.hash (TranscriptSuccess.readParts absorbed 2#u8) = .ok nextState ∧
        after = {self with state := nextState} ∧
        AspisR1GammaCaller.sampler.gamma_sample candidateGammaHelpers block' = .ok sample ∧
        Canonical digits ∧
        AspisR1.SamplerAddDigits.digitsValue AspisR1.SamplerMachineBounds.P (values digits) =
          AspisR1.SourceSamplerByteRank.rank block' %
            (AspisR1.SamplerMachineBounds.P ^ 8 - 1) + 1 ∧
        OrdinaryCandidateSourceModel.decode out =
          R0C.ModuloField.fieldRank ⟨
            AspisR1.SourceSamplerByteRank.rank block' %
              (AspisR1.SamplerMachineBounds.P ^ 8 - 1) + 1, by
            have hb := (AspisR1.SamplerNatModel.gammaDigits_value_bounds
              (AspisR1.SourceSamplerByteRank.rank_lt block')).2
            rw [AspisR1.SamplerNatModel.gammaDigits_value
              (AspisR1.SourceSamplerByteRank.rank_lt block')] at hb
            simpa [AspisR1.SamplerMachineBounds.P,
              AspisCircleGroupOrder.P] using hb⟩ := by
  obtain ⟨out, hscalar⟩ := scalar_true_total_of_block_success
    D self after payload block hblock
  refine ⟨out, hscalar, ?_⟩
  exact scalar_true_success_fieldRank D self after payload out hscalar

#print axioms scalar_true_block_success_fieldRank

end AspisR1Post25Transcript.GammaCandidateSourceModel
