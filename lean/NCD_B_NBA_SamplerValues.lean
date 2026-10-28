-- Inherited body, import-only deployed-cohort retarget.
import NCD_B_NBA_Scalars
import GammaCandidateTotalityV14
import IndexedCandidateOrdinaryRetainedBridgeV5
set_option autoImplicit false
noncomputable section
namespace AspisR1.NBA_SamplerValues
open Aeneas Aeneas.Std Result AspisR1PublicPreparation AspisR1ClaimPreparedBridge
open AspisR1CurrentPreparedClaim.Concrete

theorem gamma (block : Array U8 32#usize) :
    ∃ out, NBA_Installed.actual.sampling.gamma block=ok out ∧
      Canonical (toClaimE out) ∧ GammaRankMeaning block out := by
  obtain ⟨raw,call⟩ := AspisR1GammaCaller.DigitsModel.candidate_gamma_total block
  have mapped : candidateGammaPublic block=ok (gammaToPublic raw) := by
    unfold candidateGammaPublic
    rw [call,bind_tc_ok]
  exact ⟨gammaToPublic raw,mapped,candidateGammaPublic_success_canonical _ _ mapped,
    candidateGammaPublic_success_rank _ _ mapped⟩

/-- Ordinary output is the actual returned candidate carrier, with all words
preserved by its public port; canonicality follows from that producing call. -/
theorem ordinary (block : Array U8 32#usize) :
    ∃ raw, AspisR1Post25Sampler.sampler.ordinary_sample block=ok raw ∧
      NBA_Installed.actual.sampling.ordinary block=
        ok (AspisR1Post25SamplerPreparedCarrier.candidateToPE raw) ∧
      Canonical (toClaimE (AspisR1Post25SamplerPreparedCarrier.candidateToPE raw)) := by
  obtain ⟨raw,call,rank⟩ :=
    AspisR1.ExtractedQM31SamplerIndexedOrdinaryRetainedBridgeV5.ordinary_sample_candidate_eq_fieldRank block
  have mapped : AspisR1Post25SamplerOrdinaryCallbackV2.candidateOrdinaryPublic block=
      ok (AspisR1Post25SamplerPreparedCarrier.candidateToPE raw) := by
    unfold AspisR1Post25SamplerOrdinaryCallbackV2.candidateOrdinaryPublic
    rw [call,bind_tc_ok]
  exact ⟨raw,call,mapped,
    AspisR1Post25SamplerOrdinaryCallbackV2.candidateOrdinaryPublic_success_canonical _ _ mapped⟩

/-- Exact scalar-call replay after its three linked digest observations. -/
theorem scalar {H : Type} (D : aspis_core.Digest32 H)
    (before after : transcript.Transcript H) (row : U8) (payload : Slice U8)
    (block : Array U8 32#usize) (out : PE) (nonzero : Bool)
    (call : transcript.Transcript.block D before row payload=ok (block,after))
    (sample : (if nonzero then NBA_Installed.actual.sampling.gamma block
      else NBA_Installed.actual.sampling.ordinary block)=ok out) :
    PreparedModel.scalar NBA_Installed.actual.sampling D before row payload nonzero=ok (out,after) := by
  unfold PreparedModel.scalar
  rw [call,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [sample,bind_tc_ok]
  rfl

#print axioms gamma
#print axioms ordinary
#print axioms scalar
end AspisR1.NBA_SamplerValues
end
