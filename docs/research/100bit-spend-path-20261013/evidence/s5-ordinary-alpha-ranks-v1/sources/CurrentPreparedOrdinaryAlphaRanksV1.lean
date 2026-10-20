import CurrentPreparedOrdinaryRankV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1Post25SamplerOrdinaryAlphaRanksV1
open AspisR1CurrentPreparedClaim.Concrete
open AspisR1ClaimPreparedBridge
open AspisR1Post25SamplerOrdinaryRankV1
abbrev PE := AspisR1Post25SamplerOrdinaryRankV1.PE

def OrdinaryAlphaRankData {H : Type}
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (v : AspisR1PublicPreparation.verifier.View)
    (out : AspisR1PublicPreparation.verifier.Prepared) : Prop :=
  ∃ (alpha0 : PE) (block0 : Array U8 32#usize)
    (before after : AspisR1PublicPreparation.transcript.Transcript H),
    AspisR1PublicPreparation.transcript.Transcript.block D before 29#u8
      v.round0 = ok (block0, after) ∧
    OrdinaryRankMeaning block0 alpha0 ∧
    (out.alpha = Array.make 2#usize [alpha0,
        AspisR1PublicPreparation.aspis_core.field.WideExact.ZERO] ∨
      ∃ (alpha1 : PE) (block1 : Array U8 32#usize)
        (payload : Slice U8) (afterAlpha : AspisR1PublicPreparation.transcript.Transcript H),
        AspisR1PublicPreparation.transcript.Transcript.block D after 30#u8
          payload = ok (block1, afterAlpha) ∧
        OrdinaryRankMeaning block1 alpha1 ∧
        out.alpha = Array.make 2#usize [alpha0, alpha1])


theorem prepared_candidate_ordinary_alpha_ranks {H : Type}
    (sampling : PreparedBoundaries)
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
    (v : AspisR1PublicPreparation.verifier.View) (hash : H)
    (out : AspisR1PublicPreparation.verifier.Prepared)
    (scratch scratchIn : Array PE 29#usize)
    (h : AspisR1PublicPreparation.PreparedScratchModel.prepare
      (concreteBoundaries (AspisR1Post25SamplerOrdinaryCallbackV2.withCandidateOrdinary sampling))
      D sem v hash scratchIn = ok (.Ok out, scratch)) :
    OrdinaryAlphaRankData D v out := by
  obtain ⟨start,t1,t2,t3,bytes,gamma,kappa,alpha0,hseed,hg,hb,hk,ha,ht⟩ :=
    AspisR1PublicPreparation.PreparedScratchReachability.prepare_success
      (concreteBoundaries (AspisR1Post25SamplerOrdinaryCallbackV2.withCandidateOrdinary sampling))
      D sem v hash out scratch scratchIn h
  obtain ⟨block0,hblock0,hrank0⟩ :=
    scalar_candidate_ordinary_rank sampling D t2 t3 29#u8 v.round0 alpha0 ha
  refine ⟨alpha0,block0,t2,t3,hblock0,hrank0,?_⟩
  cases ht with
  | single hfolds htail =>
      obtain ⟨queries,afterQueries,last,rho,claim,hq,hr,hp,hc,he⟩ := htail
      subst out
      exact Or.inl rfl
  | double hfolds root bytes1 bytes2 alpha1 afterAlpha hroot hbytes1 hbytes2 halpha1 htail =>
      obtain ⟨block1,hblock1,hrank1⟩ :=
        scalar_candidate_ordinary_rank sampling D t3 afterAlpha 30#u8
          (alloc.vec.Vec.deref bytes2) alpha1 halpha1
      obtain ⟨queries,afterQueries,last,rho,claim,hq,hr,hp,hc,he⟩ := htail
      subst out
      exact Or.inr ⟨alpha1,block1,alloc.vec.Vec.deref bytes2,afterAlpha,hblock1,hrank1,rfl⟩

#print axioms prepared_candidate_ordinary_alpha_ranks
end AspisR1Post25SamplerOrdinaryAlphaRanksV1
