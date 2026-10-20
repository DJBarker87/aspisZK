import CurrentSamplerOrdinaryCallbackV2
import IndexedCandidateOrdinaryRetainedBridgeV5
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1Post25SamplerOrdinaryRankV1
open AspisR1CurrentPreparedClaim.Concrete
open AspisR1ClaimPreparedBridge
abbrev PE := AspisR1Post25SamplerOrdinaryCallbackV2.PE
abbrev PreparedBoundaries := AspisR1PublicPreparation.PreparedModel.Boundaries

def OrdinaryRankMeaning (block : Array U8 32#usize) (out : PE) : Prop :=
  ∃ r : Fin (AspisCircleGroupOrder.P^8),
    r.val=AspisR1.SourceSamplerByteRank.rank block % AspisCircleGroupOrder.P^8 ∧
    decode (toClaimE out)=R0C.ModuloField.fieldRank r

private theorem bind_success {A B : Type} (m : Result A) (f : A → Result B) (v : B)
    (h : (do let x ← m; f x)=ok v) : ∃ x,m=ok x ∧ f x=ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem ordinary_decode_same (x : AspisR1Post25Sampler.field.WideExact) :
    decode (toClaimE (AspisR1Post25SamplerPreparedCarrier.candidateToPE x)) =
      AspisR1.ExtractedQM31SamplerIndexedDecode8RetainedBridgeV3.candidateWideToExact x := by
  rfl

theorem candidateOrdinaryPublic_success_rank (block : Array U8 32#usize) (out : PE)
    (h : AspisR1Post25SamplerOrdinaryCallbackV2.candidateOrdinaryPublic block=ok out) :
    OrdinaryRankMeaning block out := by
  obtain ⟨value,hvalue,hfield⟩ :=
    AspisR1.ExtractedQM31SamplerIndexedOrdinaryRetainedBridgeV5.ordinary_sample_candidate_eq_fieldRank block
  unfold AspisR1Post25SamplerOrdinaryCallbackV2.candidateOrdinaryPublic at h
  obtain ⟨x,hx,hmap⟩ := bind_success _ _ _ h
  have hsame : x=value := Result.ok.inj (hx.symm.trans hvalue)
  have hout : AspisR1Post25SamplerPreparedCarrier.candidateToPE value=out := by
    rw [←hsame]
    exact Result.ok.inj hmap
  have hP : 0 < AspisCircleGroupOrder.P := by norm_num [AspisCircleGroupOrder.P]
  let r : Fin (AspisCircleGroupOrder.P^8) :=
    ⟨AspisR1.SourceSamplerByteRank.rank block % AspisCircleGroupOrder.P^8,
      Nat.mod_lt _ (Nat.pow_pos hP)⟩
  refine ⟨r,rfl,?_⟩
  rw [←hout,ordinary_decode_same]
  simpa [r] using hfield

theorem scalar_candidate_ordinary_rank {H : Type}
    (sampling : PreparedBoundaries)
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (before after : AspisR1PublicPreparation.transcript.Transcript H)
    (row : U8) (payload : Slice U8) (out : PE)
    (h : AspisR1PublicPreparation.PreparedModel.scalar
      (AspisR1Post25SamplerOrdinaryCallbackV2.withCandidateOrdinary sampling)
      D before row payload false=ok (out,after)) :
    ∃ block : Array U8 32#usize,
      AspisR1PublicPreparation.transcript.Transcript.block D before row payload=ok (block,after) ∧
      OrdinaryRankMeaning block out := by
  unfold AspisR1PublicPreparation.PreparedModel.scalar at h
  obtain ⟨p,hblock,h⟩ := bind_success _ _ _ h
  rcases p with ⟨block,t⟩
  simp only [AspisR1Post25SamplerOrdinaryCallbackV2.withCandidateOrdinary] at h
  obtain ⟨value,hvalue,h⟩ := bind_success _ _ _ h
  obtain ⟨i,hi,h⟩ := bind_success _ _ _ h
  obtain ⟨u,htrace,h⟩ := bind_success _ _ _ h
  have he : (value,t)=(out,after) := Result.ok.inj h
  have hout : value=out := congrArg Prod.fst he
  have ht : t=after := congrArg Prod.snd he
  refine ⟨block,by simpa only [ht] using hblock,?_⟩
  rw [←hout]
  exact candidateOrdinaryPublic_success_rank block value hvalue

theorem prepared_candidate_ordinary_rank {H : Type}
    (sampling : PreparedBoundaries)
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
    (v : AspisR1PublicPreparation.verifier.View) (hash : H)
    (out : AspisR1PublicPreparation.verifier.Prepared) (scratch scratchIn : Array PE 29#usize)
    (h : AspisR1PublicPreparation.PreparedScratchModel.prepare
      (concreteBoundaries (AspisR1Post25SamplerOrdinaryCallbackV2.withCandidateOrdinary sampling))
      D sem v hash scratchIn=ok (.Ok out,scratch)) :
    ∃ (start before after : AspisR1PublicPreparation.transcript.Transcript H)
      (block bytes : Array U8 32#usize),
      AspisR1PublicPreparation.transcript.Transcript.new D hash sem.transcript.state v.variant=ok start ∧
      AspisR1PublicPreparation.transcript.Transcript.block D before 28#u8
        (Array.to_slice bytes) = ok (block,after) ∧
      OrdinaryRankMeaning block out.kappa := by
  obtain ⟨start,t1,t2,t3,bytes,gamma,kappa,alpha0,hseed,hg,hb,hk,ha,ht⟩ :=
    AspisR1PublicPreparation.PreparedScratchReachability.prepare_success
      (concreteBoundaries (AspisR1Post25SamplerOrdinaryCallbackV2.withCandidateOrdinary sampling))
      D sem v hash out scratch scratchIn h
  obtain ⟨block,hblock,hrank⟩ :=
    scalar_candidate_ordinary_rank sampling D t1 t2 28#u8 (Array.to_slice bytes) kappa hk
  have he := (tail_concrete_run (AspisR1Post25SamplerOrdinaryCallbackV2.withCandidateOrdinary sampling)
    D sem v gamma kappa alpha0 t3 out scratch ht).2.1
  exact ⟨start,t1,t2,block,bytes,hseed,hblock,by simpa only [he] using hrank⟩
end AspisR1Post25SamplerOrdinaryRankV1

#print axioms ordinary_decode_same
#print axioms candidateOrdinaryPublic_success_rank
#print axioms scalar_candidate_ordinary_rank
#print axioms prepared_candidate_ordinary_rank
