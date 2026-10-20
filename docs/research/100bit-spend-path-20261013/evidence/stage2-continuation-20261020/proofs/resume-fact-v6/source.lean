import Stage2ContinuationResumeBody
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1Stage2
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

/-- The complete emitted decoder can return successfully only after comparing the
rehash of the proof with bytes 16..48. Equality of the comparison implementation
is the explicitly named backend premise; later decoding operations are arbitrary. -/
theorem resume_rehash_checkpoint_field (ops : ResumeOps) {H : Type}
    (digestInst : aspis_core.digest.Digest32 H)
    (ne_sound : ∀ (s : Slice U8) (a : Array U8 32#usize),
      ops.ne core.cmp.PartialEqU8 s a = ok false → s.val = a.val)
    (bytes proof public1 : Slice U8) (v : transport.Variant) (hash : H)
    (p : verifier.Prepared) (acc : verifier.Accumulator)
    (success : verifier.resumeWithOps ops digestInst bytes proof public1 v hash =
      ok (.Ok (p,acc))) :
    ∃ (stored : Slice U8) (chunks : Slice (Slice U8)) (digest : Array U8 32#usize),
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes
        { start := 16#usize, «end» := 48#usize } = ok stored ∧
      lift (Array.to_slice (Array.make 1#usize [proof])) = ok chunks ∧
      digestInst.digest hash chunks = ok digest ∧ stored.val = digest.val := by
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
  obtain ⟨end1, _, h⟩ := resume_bind_success _ _ _ h
  obtain ⟨stored, hstored, h⟩ := resume_bind_success _ _ _ h
  obtain ⟨chunks, hchunks, h⟩ := resume_bind_success _ _ _ h
  obtain ⟨digest, hdigest, h⟩ := resume_bind_success _ _ _ h
  obtain ⟨bad, hbad, h⟩ := resume_bind_success _ _ _ h
  obtain ⟨hb, _⟩ := checkpoint_guard _ _ _ h
  exact ⟨stored,chunks,digest,hstored,hchunks,hdigest,
    ne_sound stored digest (hb ▸ hbad)⟩
#print axioms checkpoint_guard_prop
#print axioms checkpoint_guard
#print axioms resume_bind_success
#print axioms resume_rehash_checkpoint_field
end AspisR1Stage2
