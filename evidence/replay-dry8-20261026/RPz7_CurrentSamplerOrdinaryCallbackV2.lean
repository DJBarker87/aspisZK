import RPz7_CurrentSamplerPreparedCarrierBoundsV1
import RPz7_CurrentPreparedOriginalPayload
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1Post25SamplerOrdinaryCallbackV2
open AspisR1CurrentPreparedClaim.Concrete
open AspisR1ClaimPreparedBridge
abbrev PE := AspisR1ClaimPreparedBridge.PE
abbrev PreparedBoundaries := AspisR1PublicPreparation.PreparedModel.Boundaries

def candidateOrdinaryPublic (block : Array U8 32#usize) : Result PE := do
  let x ← AspisR1Post25Sampler.sampler.ordinary_sample block
  ok (AspisR1Post25SamplerPreparedCarrier.candidateToPE x)

def withCandidateOrdinary (sampling : PreparedBoundaries) : PreparedBoundaries :=
  {sampling with ordinary := candidateOrdinaryPublic}

private theorem bind_success {A B : Type} (m : Result A) (f : A → Result B) (v : B)
    (h : (do let x ← m; f x)=ok v) : ∃ x,m=ok x ∧ f x=ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem candidateOrdinaryPublic_success_canonical
    (bytes : Array U8 32#usize) (out : PE)
    (h : candidateOrdinaryPublic bytes=ok out) : Canonical (toClaimE out) := by
  obtain ⟨x,hraw,hmap⟩ := bind_success _ _ _ h
  have hbound := AspisR1Post25SamplerPreparedCarrier.ordinary_sample_success_CE_coordinate_bounds bytes x hraw
  have heq : out=AspisR1Post25SamplerPreparedCarrier.candidateToPE x := Result.ok.inj hmap.symm
  rw [heq]
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := hbound
  exact ⟨⟨⟨h0,h1⟩,⟨h2,h3⟩⟩,⟨⟨h4,h5⟩,⟨h6,h7⟩⟩⟩

theorem scalar_candidate_ordinary_canonical {H : Type}
    (sampling : PreparedBoundaries)
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (before after : AspisR1PublicPreparation.transcript.Transcript H)
    (row : U8) (payload : Slice U8) (out : PE)
    (h : AspisR1PublicPreparation.PreparedModel.scalar (withCandidateOrdinary sampling)
      D before row payload false=ok (out,after)) : Canonical (toClaimE out) := by
  unfold AspisR1PublicPreparation.PreparedModel.scalar at h
  obtain ⟨p,hblock,h⟩ := bind_success _ _ _ h
  rcases p with ⟨block,t⟩
  simp only [withCandidateOrdinary,ite_false] at h
  obtain ⟨value,hvalue,h⟩ := bind_success _ _ _ h
  obtain ⟨i,hi,h⟩ := bind_success _ _ _ h
  obtain ⟨u,htrace,h⟩ := bind_success _ _ _ h
  have he : value=out := congrArg Prod.fst (Result.ok.inj h)
  rw [←he]
  exact candidateOrdinaryPublic_success_canonical block value hvalue

theorem prepared_candidate_ordinary_kappa_canonical {H : Type}
    (sampling : PreparedBoundaries)
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
    (v : AspisR1PublicPreparation.verifier.View) (hash : H)
    (out : AspisR1PublicPreparation.verifier.Prepared) (scratch scratchIn : Array PE 29#usize)
    (h : AspisR1PublicPreparation.PreparedScratchModel.prepare
      (concreteBoundaries (withCandidateOrdinary sampling)) D sem v hash scratchIn=ok (.Ok out,scratch)) :
    Canonical (toClaimE out.kappa) := by
  obtain ⟨start,t1,t2,t3,bytes,gamma,kappa,alpha0,hseed,hg,hb,hk,ha,ht⟩ :=
    AspisR1PublicPreparation.PreparedScratchReachability.prepare_success
      (concreteBoundaries (withCandidateOrdinary sampling)) D sem v hash out scratch scratchIn h
  have hc := scalar_candidate_ordinary_canonical sampling D t1 t2 28#u8
    (Array.to_slice bytes) kappa hk
  have he := (tail_concrete_run (withCandidateOrdinary sampling) D sem v gamma kappa alpha0
    t3 out scratch ht).2.1
  rw [he]
  exact hc

#print axioms candidateOrdinaryPublic_success_canonical
#print axioms scalar_candidate_ordinary_canonical
#print axioms prepared_candidate_ordinary_kappa_canonical
end AspisR1Post25SamplerOrdinaryCallbackV2
