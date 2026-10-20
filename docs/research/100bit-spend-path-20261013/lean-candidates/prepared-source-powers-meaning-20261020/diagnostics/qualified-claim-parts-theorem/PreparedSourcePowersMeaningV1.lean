import PreparedSourcePowersBoundariesV1
import CurrentPreparedCandidateSamplers
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PreparedSourcePowersMeaningV1
open AspisR1ClaimPreparedBridge AspisR1CurrentPreparedClaim
open AspisR1PreparedSourcePowersBoundariesV1
open AspisR1PublicPreparation.PreparedScratchReachability

/-- Installed gamma/ordinary sampler successes supply the canonical inputs
needed to replace the original generated powers interface. Neither gamma
nor kappa canonicality nor an internal powers/callback run is a premise. -/
theorem prepared_sourcePowers_claim_meaning {H : Type}
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
    (v : AspisR1PublicPreparation.verifier.View) (hash : H)
    (out : AspisR1PublicPreparation.verifier.Prepared) (scratch scratchIn : Array PE 29#usize)
    (hinactive : Concrete.Canonical (toClaimE v.inactive))
    (h : AspisR1PublicPreparation.PreparedScratchModel.prepare
      (sourceBoundaries (withCandidateSamplers sampling)) D sem v hash scratchIn=ok (.Ok out,scratch)) :
    (Concrete.Canonical (toClaimE out.gamma) ∧ Concrete.Canonical (toClaimE out.kappa)) ∧
    ClaimSourceMeaning (toClaimSem sem) v.y1 (toClaimE v.inactive)
      (toClaimE out.gamma) (toClaimE out.kappa) (toClaimE out.claim)
      (mapArray toClaimE scratch) := by
  obtain ⟨start,t1,t2,t3,bytes,gamma,kappa,alpha0,hseed,hg,hb,hk,ha,ht⟩ :=
    prepare_success (sourceBoundaries (withCandidateSamplers sampling))
      D sem v hash out scratch scratchIn h
  have hgc := scalar_candidate_gamma_canonical
    (AspisR1Post25SamplerOrdinaryCallbackV2.withCandidateOrdinary sampling)
    D start t1 27#u8 v.y1 gamma hg
  have hks : AspisR1PublicPreparation.PreparedModel.scalar
      (AspisR1Post25SamplerOrdinaryCallbackV2.withCandidateOrdinary (withCandidateGamma sampling))
      D t1 28#u8 (Array.to_slice bytes) false=ok (kappa,t2) := by
    change AspisR1PublicPreparation.PreparedModel.scalar (withCandidateSamplers sampling)
      D t1 28#u8 (Array.to_slice bytes) false=ok (kappa,t2) at hk
    rw [candidate_sampler_updates_commute] at hk
    exact hk
  have hkc := AspisR1Post25SamplerOrdinaryCallbackV2.scalar_candidate_ordinary_canonical
    (withCandidateGamma sampling) D t1 t2 28#u8 (Array.to_slice bytes) kappa hks
  have htail := sourceTail_transport (withCandidateSamplers sampling) D sem v
    gamma kappa alpha0 t3 out scratch hgc hkc ht
  obtain ⟨hgamma,hkappa,hrun⟩ := tail_concrete_run
    (withCandidateSamplers sampling) D sem v gamma kappa alpha0 t3 out scratch htail
  have hgc' : Concrete.Canonical (toClaimE out.gamma) := by rw [hgamma]; exact hgc
  have hkc' : Concrete.Canonical (toClaimE out.kappa) := by rw [hkappa]; exact hkc
  refine ⟨⟨hgc',hkc'⟩,?_⟩
  exact successful_claim_source_gamma_kappa_sum (toClaimDigest D) (toClaimSem sem) v.y1
    (toClaimE v.inactive) (toClaimE out.gamma) (toClaimE out.kappa) (toClaimE out.claim)
    (mapArray toClaimE scratch) hgc' hkc' hinactive hrun.1 hrun.2

#print axioms prepared_sourcePowers_claim_meaning
end AspisR1PreparedSourcePowersMeaningV1
