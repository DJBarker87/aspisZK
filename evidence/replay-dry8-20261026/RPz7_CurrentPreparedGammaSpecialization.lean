import RPz7_CurrentPreparedGammaCallback
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1ClaimPreparedBridge
open AspisR1CurrentPreparedClaim.Concrete

private theorem bind_success {A B : Type} (m : Result A) (f : A → Result B) (v : B)
    (h : (do let x ← m; f x)=ok v) : ∃ x,m=ok x ∧ f x=ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

def withCandidateGamma (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries) :
    AspisR1PublicPreparation.PreparedModel.Boundaries :=
  {sampling with gamma:=candidateGammaPublic}

theorem scalar_candidate_gamma_canonical {H : Type}
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (before after : AspisR1PublicPreparation.transcript.Transcript H)
    (row : U8) (payload : Slice U8) (out : PE)
    (h : AspisR1PublicPreparation.PreparedModel.scalar (withCandidateGamma sampling)
      D before row payload true=ok (out,after)) : Canonical (toClaimE out) := by
  unfold AspisR1PublicPreparation.PreparedModel.scalar at h
  obtain ⟨p,hblock,h⟩ := bind_success _ _ _ h
  rcases p with ⟨block,t⟩
  simp only [withCandidateGamma,ite_true] at h
  obtain ⟨value,hvalue,h⟩ := bind_success _ _ _ h
  obtain ⟨i,hi,h⟩ := bind_success _ _ _ h
  obtain ⟨u,htrace,h⟩ := bind_success _ _ _ h
  have he : value=out := congrArg Prod.fst (Result.ok.inj h)
  rw [←he]
  exact candidateGammaPublic_success_canonical block value hvalue

theorem prepared_candidate_gamma_canonical {H : Type}
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
    (v : AspisR1PublicPreparation.verifier.View) (hash : H)
    (out : AspisR1PublicPreparation.verifier.Prepared) (scratch scratchIn : Array PE 29#usize)
    (h : AspisR1PublicPreparation.PreparedScratchModel.prepare
      (concreteBoundaries (withCandidateGamma sampling)) D sem v hash scratchIn=ok (.Ok out,scratch)) :
    Canonical (toClaimE out.gamma) := by
  obtain ⟨start,t1,t2,t3,bytes,gamma,kappa,alpha0,hseed,hg,hb,hk,ha,ht⟩ :=
    AspisR1PublicPreparation.PreparedScratchReachability.prepare_success
      (concreteBoundaries (withCandidateGamma sampling)) D sem v hash out scratch scratchIn h
  have hc := scalar_candidate_gamma_canonical sampling D start t1 27#u8 v.y1 gamma hg
  have he := (tail_concrete_run (withCandidateGamma sampling) D sem v gamma kappa alpha0
    t3 out scratch ht).1
  rw [he]
  exact hc

theorem prepared_candidate_gamma_original_payload {H : Type}
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
    (v : AspisR1PublicPreparation.verifier.View) (hash : H)
    (out : AspisR1PublicPreparation.verifier.Prepared) (scratch scratchIn : Array PE 29#usize)
    (hkappa : Canonical (toClaimE out.kappa)) (hinactive : Canonical (toClaimE v.inactive))
    (h : AspisR1PublicPreparation.PreparedScratchModel.prepare
      (concreteBoundaries (withCandidateGamma sampling)) D sem v hash scratchIn=ok (.Ok out,scratch)) :
    OriginalPayloadClaimMeaning sem v.y1 (toClaimE v.inactive)
      (toClaimE out.gamma) (toClaimE out.kappa) (toClaimE out.claim)
      (mapArray toClaimE scratch) := by
  exact prepared_success_original_payload_claim (withCandidateGamma sampling) D sem v hash
    out scratch scratchIn (prepared_candidate_gamma_canonical sampling D sem v hash out scratch scratchIn h)
    hkappa hinactive h

#print axioms scalar_candidate_gamma_canonical
#print axioms prepared_candidate_gamma_canonical
#print axioms prepared_candidate_gamma_original_payload
end AspisR1ClaimPreparedBridge
