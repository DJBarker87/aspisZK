import CurrentPreparedAlphaCanonical
import ExtractedDigest32SamplerTransport
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1ClaimPreparedBridge.CurrentRho
open AspisR1PublicPreparation
open AspisR1PublicPreparation.PreparedScratchReachability

private theorem bind_success {A B : Type} (m : Result A) (f : A → Result B) (v : B)
    (h : (do let x ← m; f x)=ok v) : ∃ x,m=ok x ∧ f x=ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
private theorem pair_bind_success {A B C : Type} (m : Result (A × B))
    (f : A → B → Result C) (v : C)
    (h : (do let (a,b) ← m; f a b)=ok v) :
    ∃ a b,m=ok (a,b) ∧ f a b=ok v := by
  cases m with
  | ok pair => cases pair with | mk a b => exact ⟨a,b,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

-- Reused rho_success proof from ExtractedOpeningCalls, with current minimal imports.
theorem scalar_k_success {H : Type} (B : PreparedModel.Boundaries) (D : aspis_core.Digest32 H)
    (self after : transcript.Transcript H) (row : U8) (payload : Slice U8)
    (out : aspis_core.field.QM31)
    (h : PreparedModel.scalar_k B D self row payload=ok (out,after)) :
    ∃ block,transcript.Transcript.block D self row payload=ok (block,after) ∧
      sampler.qm31_sample block=ok out := by
  unfold PreparedModel.scalar_k at h
  obtain ⟨block,mid,hblock,h⟩ := pair_bind_success _ _ _ h
  obtain ⟨value,hvalue,h⟩ := bind_success _ _ _ h
  simp only [lift,bind_tc_ok] at h
  obtain ⟨wide,hwide,h⟩ := bind_success _ _ _ h
  obtain ⟨mark,htrace,h⟩ := bind_success _ _ _ h
  cases mark
  have he := Result.ok.inj h
  have hv : value=out := congrArg Prod.fst he
  have ht : mid=after := congrArg Prod.snd he
  exact ⟨block,by simpa only [ht] using hblock,by simpa only [hv] using hvalue⟩

def RhoAfterQueryFacts {H : Type} (B : PreparedModel.Boundaries) (D : aspis_core.Digest32 H)
    (v : verifier.View) (out : verifier.Prepared) (row : U8) (before : transcript.Transcript H) : Prop :=
  ∃ (afterQueries last : transcript.Transcript H) (block : Array U8 32#usize),
    B.queries D before row v.final_message=ok (.Ok out.queries,afterQueries) ∧
    transcript.Transcript.block D afterQueries (if row=30#u8 then 31#u8 else 32#u8)
      emptyPayload=ok (block,last) ∧
    sampler.qm31_sample block=ok out.rho ∧
    AspisR1.ExtractedQM31SamplerCarrier.CurrentCanonicalQM
      (AspisR1.ExtractedQM31SamplerCarrier.toCurrent (SamplerTransport.toOld out.rho)) ∧
    AspisR1.ExtractedQM31SamplerCorrect.coordinates (SamplerTransport.toOld out.rho)=
      AspisR1.SamplerNatModel.qm31Digits (AspisR1.SourceSamplerByteRank.rank block) ∧
    out.state=last.state

theorem afterQueries_rho_meaning {H : Type} (B : PreparedScratchModel.Boundaries)
    (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H) (v : verifier.View)
    (gamma kappa : PE) (alpha : Array PE 2#usize) (row : U8) (before : transcript.Transcript H)
    (out : verifier.Prepared) (scratch : Array PE 29#usize)
    (h : AfterQueries B D sem v gamma kappa alpha row before out scratch) :
    RhoAfterQueryFacts B.sampling D v out row before := by
  obtain ⟨queries,afterQueries,last,rho,claim,hq,hr,hp,hc,he⟩ := h
  obtain ⟨block,hblock,hsample⟩ := scalar_k_success B.sampling D afterQueries last
    (if row=30#u8 then 31#u8 else 32#u8) emptyPayload rho hr
  obtain ⟨q0,hq0,hcanonical,hcoords⟩ := SamplerTransport.sample_total block
  have hsame : q0=rho := Result.ok.inj (hq0.symm.trans hsample)
  subst q0
  subst out
  exact ⟨afterQueries,last,block,hq,hblock,hsample,hcanonical,hcoords,rfl⟩

theorem tail_rho_meaning {H : Type} (B : PreparedScratchModel.Boundaries)
    (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H) (v : verifier.View)
    (gamma kappa alpha0 : PE) (before : transcript.Transcript H)
    (out : verifier.Prepared) (scratch : Array PE 29#usize)
    (h : Tail B D sem v gamma kappa alpha0 before out scratch) :
    ∃ (row : U8) (queryBefore : transcript.Transcript H),
      (row=30#u8 ∨ row=31#u8) ∧ RhoAfterQueryFacts B.sampling D v out row queryBefore := by
  cases h with
  | single hf ha => exact ⟨30#u8,before,Or.inl rfl,afterQueries_rho_meaning B D sem v gamma kappa _ _ _ out scratch ha⟩
  | double hf root bytes1 bytes2 alpha1 afterAlpha hroot hb1 hb2 halpha1 ha =>
    exact ⟨31#u8,afterAlpha,Or.inr rfl,afterQueries_rho_meaning B D sem v gamma kappa _ _ _ out scratch ha⟩

theorem prepared_success_rho_meaning {H : Type} (B : PreparedScratchModel.Boundaries)
    (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
    (out : verifier.Prepared) (scratch scratchIn : Array PE 29#usize)
    (h : PreparedScratchModel.prepare B D sem v hash scratchIn=ok (.Ok out,scratch)) :
    ∃ (row : U8) (queryBefore : transcript.Transcript H),
      (row=30#u8 ∨ row=31#u8) ∧ RhoAfterQueryFacts B.sampling D v out row queryBefore := by
  obtain ⟨start,t1,t2,t3,bytes,gamma,kappa,alpha0,hseed,hg,hb,hk,ha,ht⟩ :=
    prepare_success B D sem v hash out scratch scratchIn h
  exact tail_rho_meaning B D sem v gamma kappa alpha0 t3 out scratch ht

#print axioms scalar_k_success
#print axioms afterQueries_rho_meaning
#print axioms tail_rho_meaning
#print axioms prepared_success_rho_meaning
end AspisR1ClaimPreparedBridge.CurrentRho
