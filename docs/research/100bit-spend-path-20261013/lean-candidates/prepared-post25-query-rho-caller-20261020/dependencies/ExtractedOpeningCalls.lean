import ExtractedPreparedReachability
import ExtractedDigest32Callers
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.OpeningCalls
open r1_wire TranscriptStep
private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
private theorem pair_bind_success {α β γ : Type} (m : Result (α × β))
    (k : α → β → Result γ) (v : γ)
    (h : (do let (a,b) ← m; k a b) = ok v) :
    ∃ a b, m = ok (a,b) ∧ k a b = ok v := by
  cases m with
  | ok pair => cases pair with | mk a b => exact ⟨a,b,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
theorem absorb_success {H : Type} (D : aspis_core.Digest32 H)
    (self after : transcript.Transcript H) (row : U8) (payload : Slice U8)
    (h : transcript.Transcript.absorb D self row payload = ok after) :
    ∃ tag state, 160#u8 + row = ok tag ∧
      D.digest self.hash (CallerStep.openingAbsorbParts self.state tag
        (UScalar.cast .U32 (Slice.len payload)) payload) = ok state ∧
      after = {self with state} := by
  simp only [transcript.Transcript.absorb,lift,bind_tc_ok] at h
  obtain ⟨tag,htag,h⟩ := bind_success _ _ _ h
  obtain ⟨state,hstate,h⟩ := bind_success _ _ _ h
  exact ⟨tag,state,htag,hstate,(Result.ok.inj h).symm⟩

theorem absorb_hash {H : Type} (D : aspis_core.Digest32 H)
    (self after : transcript.Transcript H) (row : U8) (payload : Slice U8)
    (h : transcript.Transcript.absorb D self row payload = ok after) :
    after.hash = self.hash := by
  obtain ⟨tag,state,_,_,rfl⟩ := absorb_success D self after row payload h
  rfl

theorem scalar_success {H : Type} (B : PreparedModel.Boundaries) (D : aspis_core.Digest32 H)
    (self after : transcript.Transcript H) (row : U8) (payload : Slice U8)
    (nonzero : Bool) (out : aspis_core.field.WideExact)
    (h : PreparedModel.scalar B D self row payload nonzero = ok (out,after)) :
    ∃ block, transcript.Transcript.block D self row payload = ok (block,after) ∧
      (if nonzero then B.gamma block else B.ordinary block) = ok out := by
  unfold PreparedModel.scalar at h
  obtain ⟨block,mid,hblock,h⟩ := pair_bind_success _ _ _ h
  obtain ⟨value,hvalue,h⟩ := bind_success _ _ _ h
  simp only [lift,bind_tc_ok] at h
  obtain ⟨mark,htrace,h⟩ := bind_success _ _ _ h
  cases mark
  have he := Result.ok.inj h
  have hv : value = out := congrArg Prod.fst he
  have ht : mid = after := congrArg Prod.snd he
  exact ⟨block,by simpa only [ht] using hblock,by simpa only [hv] using hvalue⟩

theorem rho_success {H : Type} (B : PreparedModel.Boundaries) (D : aspis_core.Digest32 H)
    (self after : transcript.Transcript H) (row : U8) (payload : Slice U8)
    (out : aspis_core.field.QM31)
    (h : PreparedModel.scalar_k B D self row payload = ok (out,after)) :
    ∃ block, transcript.Transcript.block D self row payload = ok (block,after) ∧
      sampler.qm31_sample block = ok out := by
  unfold PreparedModel.scalar_k at h
  obtain ⟨block,mid,hblock,h⟩ := pair_bind_success _ _ _ h
  obtain ⟨value,hvalue,h⟩ := bind_success _ _ _ h
  simp only [lift,bind_tc_ok] at h
  obtain ⟨wide,hwide,h⟩ := bind_success _ _ _ h
  obtain ⟨mark,htrace,h⟩ := bind_success _ _ _ h
  cases mark
  have he := Result.ok.inj h
  have hv : value = out := congrArg Prod.fst he
  have ht : mid = after := congrArg Prod.snd he
  exact ⟨block,by simpa only [ht] using hblock,by simpa only [hv] using hvalue⟩

/-- The actual opening constructor consumes the semantic final state. Combined
with the circle26 output equation this is the exact row26-to-opening reseed. -/
theorem prepare_reseed_success {H : Type} (B : PreparedModel.Boundaries)
    (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H) (view : verifier.View)
    (hash : H) (out : verifier.Prepared)
    (h : PreparedModel.prepare B D sem view hash = ok (.Ok out)) :
    ∃ start state gamma t1,
      D.digest hash (CallerStep.reseedParts sem.transcript.state view.variant) = ok state ∧
      start = {state,hash} ∧
      PreparedModel.scalar B D start 27#u8 view.y1 true = ok (gamma,t1) := by
  obtain ⟨start,t1,t2,t3,bytes,gamma,kappa,alpha,hseed,hgamma,_⟩ :=
    PreparedReachability.prepare_success B D sem view hash out h
  obtain ⟨state,hstate,he⟩ := CallerStep.opening_new_success D hash sem.transcript.state view.variant start hseed
  exact ⟨start,state,gamma,t1,hstate,he,hgamma⟩
#print axioms absorb_success
#print axioms absorb_hash
#print axioms scalar_success
#print axioms rho_success
#print axioms prepare_reseed_success
end AspisR1PublicPreparation.OpeningCalls
