import RPz7_CurrentPreparedGammaSpecialization
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1ClaimPreparedBridge
open AspisR1CurrentPreparedClaim.Concrete

def GammaRankMeaning (block : Array U8 32#usize) (out : PE) : Prop :=
  ∃ r : Fin (AspisCircleGroupOrder.P^8),
    r.val=AspisR1.SourceSamplerByteRank.rank block % (AspisR1.SamplerMachineBounds.P^8-1)+1 ∧
    decode (toClaimE out)=R0C.ModuloField.fieldRank r

theorem gamma_decode_same (x : AspisR1GammaCaller.DigitsModel.GammaWide) :
    decode (toClaimE (gammaToPublic x))=AspisR1GammaCaller.DigitsModel.gammaWideToExact x := by
  rfl

theorem candidateGammaPublic_success_rank (block : Array U8 32#usize) (out : PE)
    (h : candidateGammaPublic block=ok out) : GammaRankMeaning block out := by
  unfold candidateGammaPublic at h
  cases hg : AspisR1GammaCaller.sampler.gamma_sample
      AspisR1GammaCaller.DigitsModel.candidateGammaHelpers block with
  | fail e => simp only [hg,bind_tc_fail] at h; cases h
  | div => simp only [hg,bind_tc_div] at h; cases h
  | ok value =>
    simp only [hg,bind_tc_ok] at h
    have he : gammaToPublic value=out := Result.ok.inj h
    obtain ⟨digits,hd,hc,hv,hf⟩ :=
      AspisR1GammaCaller.DigitsModel.candidate_gamma_decode_fieldRank block value hg
    have hbound := (AspisR1.SamplerNatModel.gammaDigits_value_bounds
      (AspisR1.SourceSamplerByteRank.rank_lt block)).2
    rw [AspisR1.SamplerNatModel.gammaDigits_value
      (AspisR1.SourceSamplerByteRank.rank_lt block)] at hbound
    have hb : AspisR1.SourceSamplerByteRank.rank block %
        (AspisR1.SamplerMachineBounds.P^8-1)+1 < AspisCircleGroupOrder.P^8 := hbound
    let r : Fin (AspisCircleGroupOrder.P^8) := ⟨_,hb⟩
    refine ⟨r,rfl,?_⟩
    rw [←he,gamma_decode_same]
    exact hf

private theorem bind_success {A B : Type} (m : Result A) (f : A → Result B) (v : B)
    (h : (do let x ← m; f x)=ok v) : ∃ x,m=ok x ∧ f x=ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem scalar_candidate_gamma_rank {H : Type}
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (before after : AspisR1PublicPreparation.transcript.Transcript H)
    (row : U8) (payload : Slice U8) (out : PE)
    (h : AspisR1PublicPreparation.PreparedModel.scalar (withCandidateGamma sampling)
      D before row payload true=ok (out,after)) :
    ∃ block : Array U8 32#usize,
      AspisR1PublicPreparation.transcript.Transcript.block D before row payload=ok (block,after) ∧
      GammaRankMeaning block out := by
  unfold AspisR1PublicPreparation.PreparedModel.scalar at h
  obtain ⟨p,hblock,h⟩ := bind_success _ _ _ h
  rcases p with ⟨block,t⟩
  simp only [withCandidateGamma,ite_true] at h
  obtain ⟨value,hvalue,h⟩ := bind_success _ _ _ h
  obtain ⟨i,hi,h⟩ := bind_success _ _ _ h
  obtain ⟨u,htrace,h⟩ := bind_success _ _ _ h
  have he : (value,t)=(out,after) := Result.ok.inj h
  have hout : value=out := congrArg Prod.fst he
  have ht : t=after := congrArg Prod.snd he
  refine ⟨block,by simpa only [ht] using hblock,?_⟩
  rw [←hout]
  exact candidateGammaPublic_success_rank block value hvalue

theorem prepared_candidate_gamma_rank {H : Type}
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
    (v : AspisR1PublicPreparation.verifier.View) (hash : H)
    (out : AspisR1PublicPreparation.verifier.Prepared) (scratch scratchIn : Array PE 29#usize)
    (h : AspisR1PublicPreparation.PreparedScratchModel.prepare
      (concreteBoundaries (withCandidateGamma sampling)) D sem v hash scratchIn=ok (.Ok out,scratch)) :
    ∃ (start after : AspisR1PublicPreparation.transcript.Transcript H) (block : Array U8 32#usize),
      AspisR1PublicPreparation.transcript.Transcript.new D hash sem.transcript.state v.variant=ok start ∧
      AspisR1PublicPreparation.transcript.Transcript.block D start 27#u8 v.y1=ok (block,after) ∧
      GammaRankMeaning block out.gamma := by
  obtain ⟨start,t1,t2,t3,bytes,gamma,kappa,alpha0,hseed,hg,hb,hk,ha,ht⟩ :=
    AspisR1PublicPreparation.PreparedScratchReachability.prepare_success
      (concreteBoundaries (withCandidateGamma sampling)) D sem v hash out scratch scratchIn h
  obtain ⟨block,hblock,hrank⟩ := scalar_candidate_gamma_rank sampling D start t1 27#u8 v.y1 gamma hg
  have he := (tail_concrete_run (withCandidateGamma sampling) D sem v gamma kappa alpha0
    t3 out scratch ht).1
  exact ⟨start,t1,block,hseed,hblock,by simpa only [he] using hrank⟩

#print axioms gamma_decode_same
#print axioms candidateGammaPublic_success_rank
#print axioms scalar_candidate_gamma_rank
#print axioms prepared_candidate_gamma_rank
end AspisR1ClaimPreparedBridge
