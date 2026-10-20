import CurrentPreparedCandidateSamplers
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1ClaimPreparedBridge
open AspisR1CurrentPreparedClaim.Concrete

def CanonicalAlphaPair (out : AspisR1PublicPreparation.verifier.Prepared) : Prop :=
  ∃ a b : PE,out.alpha=Array.make 2#usize [a,b] ∧
    Canonical (toClaimE a) ∧ Canonical (toClaimE b)

theorem public_zero_canonical :
    Canonical (toClaimE AspisR1PublicPreparation.aspis_core.field.WideExact.ZERO) := by
  unfold AspisR1PublicPreparation.aspis_core.field.WideExact.ZERO
    AspisR1PublicPreparation.aspis_core.field.QM31.ZERO
  have h0 : (0#u32).val<2147483647 := by decide
  exact ⟨⟨⟨h0,h0⟩,⟨h0,h0⟩⟩,⟨⟨h0,h0⟩,⟨h0,h0⟩⟩⟩

theorem scalar_candidate_samplers_false_canonical {H : Type}
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (before after : AspisR1PublicPreparation.transcript.Transcript H)
    (row : U8) (payload : Slice U8) (out : PE)
    (h : AspisR1PublicPreparation.PreparedModel.scalar (withCandidateSamplers sampling)
      D before row payload false=ok (out,after)) : Canonical (toClaimE out) := by
  rw [candidate_sampler_updates_commute] at h
  exact AspisR1Post25SamplerOrdinaryCallbackV2.scalar_candidate_ordinary_canonical
    (withCandidateGamma sampling) D before after row payload out h

theorem tail_candidate_alpha_pair {H : Type}
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
    (v : AspisR1PublicPreparation.verifier.View) (gamma kappa alpha0 : PE)
    (before : AspisR1PublicPreparation.transcript.Transcript H)
    (out : AspisR1PublicPreparation.verifier.Prepared) (scratch : Array PE 29#usize)
    (hc0 : Canonical (toClaimE alpha0))
    (ht : AspisR1PublicPreparation.PreparedScratchReachability.Tail
      (concreteBoundaries (withCandidateSamplers sampling)) D sem v gamma kappa alpha0 before out scratch) :
    CanonicalAlphaPair out := by
  cases ht with
  | single hf ha =>
    obtain ⟨queries,afterQueries,last,rho,claim,hq,hr,hp,hc,he⟩ := ha
    subst out
    exact ⟨alpha0,_,rfl,hc0,public_zero_canonical⟩
  | double hf root bytes1 bytes2 alpha1 afterAlpha hroot hb1 hb2 halpha1 ha =>
    have hc1 := scalar_candidate_samplers_false_canonical sampling D before afterAlpha 30#u8
      (AspisR1PublicPreparation.alloc.vec.Vec.deref bytes2) alpha1 halpha1
    obtain ⟨queries,afterQueries,last,rho,claim,hq,hr,hp,hc,he⟩ := ha
    subst out
    exact ⟨alpha0,alpha1,rfl,hc0,hc1⟩

theorem prepared_candidate_alpha_pair {H : Type}
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
    (v : AspisR1PublicPreparation.verifier.View) (hash : H)
    (out : AspisR1PublicPreparation.verifier.Prepared) (scratch scratchIn : Array PE 29#usize)
    (h : AspisR1PublicPreparation.PreparedScratchModel.prepare
      (concreteBoundaries (withCandidateSamplers sampling)) D sem v hash scratchIn=ok (.Ok out,scratch)) :
    CanonicalAlphaPair out := by
  obtain ⟨start,t1,t2,t3,bytes,gamma,kappa,alpha0,hseed,hg,hb,hk,ha,ht⟩ :=
    AspisR1PublicPreparation.PreparedScratchReachability.prepare_success
      (concreteBoundaries (withCandidateSamplers sampling)) D sem v hash out scratch scratchIn h
  have hc0 := scalar_candidate_samplers_false_canonical sampling D t2 t3 29#u8 v.round0 alpha0 ha
  exact tail_candidate_alpha_pair sampling D sem v gamma kappa alpha0 t3 out scratch hc0 ht

#print axioms public_zero_canonical
#print axioms scalar_candidate_samplers_false_canonical
#print axioms tail_candidate_alpha_pair
#print axioms prepared_candidate_alpha_pair
end AspisR1ClaimPreparedBridge
