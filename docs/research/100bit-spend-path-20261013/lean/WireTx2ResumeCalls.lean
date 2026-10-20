import Stage2ContinuationResumeBody
import WireTx2Records
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1Stage2.WireTx2
private theorem resume_bind_success {A B : Type} (m : Result A) (k : A → Result B) (v : B)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem checkpoint_guard {T : Type} (b : Bool)
    (tail : Result (core.result.Result T verifier.Error)) (out : T)
    (h : (if b then ok (.Err verifier.Error.Checkpoint) else tail) = ok (.Ok out)) :
    b = false ∧ tail = ok (.Ok out) := by
  cases b
  · exact ⟨rfl,h⟩
  · cases h

private theorem checkpoint_guard_prop {T : Type} (b : Prop) [Decidable b]
    (tail : Result (core.result.Result T verifier.Error)) (out : T)
    (h : (if b then ok (.Err verifier.Error.Checkpoint) else tail) = ok (.Ok out)) :
    tail = ok (.Ok out) := by
  split at h
  · cases h
  · exact h


/-- All three dictionary calls on a successful complete emitted resume path.
No comparison-soundness assumption is needed to identify the input bytes. -/
theorem resume_three_inputs (ops : ResumeOps) {H : Type}
    (D : aspis_core.digest.Digest32 H)
    (bytes proof public1 : Slice U8) (v : transport.Variant) (hash : H)
    (p : verifier.Prepared) (acc : verifier.Accumulator)
    (success : verifier.resumeWithOps ops D bytes proof public1 v hash = ok (.Ok (p,acc))) :
    ∃ (end1 : Usize) (body : Slice U8) (d0 d1 d2 : Array U8 32#usize),
      Slice.len bytes - 32#usize = ok end1 ∧
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeToUsizeSlice U8) bytes
        { «end» := end1 } = ok body ∧
      D.digest hash (singletonParts proof) = ok d0 ∧
      D.digest hash (singletonParts public1) = ok d1 ∧
      D.digest hash (checksumParts body) = ok d2 := by
  unfold verifier.resumeWithOps at success
  obtain ⟨size, _, h⟩ := resume_bind_success _ _ _ success
  obtain ⟨_, h⟩ := checkpoint_guard _ _ _ h
  obtain ⟨header, _, h⟩ := resume_bind_success _ _ _ h
  obtain ⟨magicBad, _, h⟩ := resume_bind_success _ _ _ h
  obtain ⟨_, h⟩ := checkpoint_guard _ _ _ h
  obtain ⟨tagByte, _, h⟩ := resume_bind_success _ _ _ h
  obtain ⟨tag, _, h⟩ := resume_bind_success _ _ _ h
  obtain ⟨_, h⟩ := checkpoint_guard _ _ _ h
  obtain ⟨nextByte, _, h⟩ := resume_bind_success _ _ _ h
  have h := checkpoint_guard_prop _ _ _ h
  obtain ⟨version, _, h⟩ := resume_bind_success _ _ _ h
  obtain ⟨_, h⟩ := checkpoint_guard _ _ _ h
  obtain ⟨reserved, _, h⟩ := resume_bind_success _ _ _ h
  obtain ⟨iter, _, h⟩ := resume_bind_success _ _ _ h
  obtain ⟨anyResult, _, h⟩ := resume_bind_success _ _ _ h
  rcases anyResult with ⟨anyBad, iterOut⟩
  obtain ⟨_, h⟩ := checkpoint_guard _ _ _ h
  obtain ⟨end1, hend, h⟩ := resume_bind_success _ _ _ h
  obtain ⟨stored, hstored, h⟩ := resume_bind_success _ _ _ h
  obtain ⟨chunks, hchunks, h⟩ := resume_bind_success _ _ _ h
  obtain ⟨digest, hdigest, h⟩ := resume_bind_success _ _ _ h
  obtain ⟨bad, hbad, h⟩ := resume_bind_success _ _ _ h
  obtain ⟨_, h⟩ := checkpoint_guard _ _ _ h

  obtain ⟨stored1, _, h⟩ := resume_bind_success _ _ _ h
  obtain ⟨chunks1, hchunks1, h⟩ := resume_bind_success _ _ _ h
  obtain ⟨digest1, hdigest1, h⟩ := resume_bind_success _ _ _ h
  obtain ⟨bad1, _, h⟩ := resume_bind_success _ _ _ h
  obtain ⟨_, h⟩ := checkpoint_guard _ _ _ h
  obtain ⟨stored2, _, h⟩ := resume_bind_success _ _ _ h
  obtain ⟨domain, hdomain, h⟩ := resume_bind_success _ _ _ h
  obtain ⟨body, hbody, h⟩ := resume_bind_success _ _ _ h
  obtain ⟨chunks2, hchunks2, h⟩ := resume_bind_success _ _ _ h
  obtain ⟨digest2, hdigest2, _⟩ := resume_bind_success _ _ _ h
  have hc : chunks = singletonParts proof := by
    simpa [lift, singletonParts] using hchunks.symm
  have hc1 : chunks1 = singletonParts public1 := by
    simpa [lift, singletonParts] using hchunks1.symm
  have hdom : domain = checksumDomain := by
    simpa [lift, checksumDomain] using hdomain.symm
  have hc2 : chunks2 = checksumParts body := by
    simpa [lift, checksumParts, hdom] using hchunks2.symm
  exact ⟨end1, body, digest, digest1, digest2, hend, hbody,
    hc ▸ hdigest, hc1 ▸ hdigest1, hc2 ▸ hdigest2⟩

/-- Caller widths classify the first two calls. The checksum body width is
an explicit slice/size boundary, not an assumption of checkpoint authenticity. -/
theorem resume_binding_inputs_typed (proof public1 body : Slice U8)
    (hp : proof.val.length = 57607) (ha : public1.val.length = 1880)
    (hb : body.val.length = 1736) :
    TypedInput (singletonParts proof) ∧ TypedInput (singletonParts public1) ∧
      TypedInput (checksumParts body) :=
  ⟨.proof proof hp, .publicAccount public1 ha, .checksum body hb⟩
#print axioms resume_bind_success
#print axioms checkpoint_guard
#print axioms checkpoint_guard_prop
#print axioms resume_three_inputs
#print axioms resume_binding_inputs_typed
end AspisR1Stage2.WireTx2
