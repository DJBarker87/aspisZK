import Stage2ContinuationResume
/-! The three checkpoint authentication calls, extracted from successful resume.
No decoder or arithmetic backend correctness is assumed beyond comparison soundness. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1Stage2.Tx2ResumeDigests
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

structure Calls {H : Type} (D : aspis_core.digest.Digest32 H)
    (hash : H) (bytes proof public1 : Slice U8) where
  storedProof : Slice U8
  storedPublic : Slice U8
  storedChecksum : Slice U8
  proofParts : Slice (Slice U8)
  publicParts : Slice (Slice U8)
  checksumParts : Slice (Slice U8)
  proofDigest : Array U8 32#usize
  publicDigest : Array U8 32#usize
  checksumDigest : Array U8 32#usize
  checksumEnd : Usize
  end_eq : Slice.len bytes - 32#usize = ok checksumEnd
  proofField : core.slice.index.Slice.index
    (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes
    {start := 16#usize, «end» := 48#usize} = ok storedProof
  publicField : core.slice.index.Slice.index
    (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes
    {start := 48#usize, «end» := 80#usize} = ok storedPublic
  checksumField : core.slice.index.Slice.index
    (core.slice.index.SliceIndexRangeFromUsizeSlice U8) bytes
    {start := checksumEnd} = ok storedChecksum
  proofInput : lift (Array.to_slice (Array.make 1#usize [proof])) = ok proofParts
  publicInput : lift (Array.to_slice (Array.make 1#usize [public1])) = ok publicParts
  checksumDomain : Slice U8
  checksumBody : Slice U8
  domainInput : lift (Array.to_slice (Array.make 22#usize [
    85#u8, 78#u8, 80#u8, 82#u8, 79#u8, 86#u8, 69#u8, 68#u8,
    58#u8, 82#u8, 49#u8, 58#u8, 99#u8, 104#u8, 101#u8,
    99#u8, 107#u8, 112#u8, 111#u8, 105#u8, 110#u8, 116#u8])) = ok checksumDomain
  bodyInput : core.slice.index.Slice.index
    (core.slice.index.SliceIndexRangeToUsizeSlice U8) bytes
    {«end» := checksumEnd} = ok checksumBody
  checksumInput : lift (Array.to_slice
    (Array.make 2#usize [checksumDomain, checksumBody])) = ok checksumParts
  proofCall : D.digest hash proofParts = ok proofDigest
  publicCall : D.digest hash publicParts = ok publicDigest
  checksumCall : D.digest hash checksumParts = ok checksumDigest
  proofEqual : storedProof.val = proofDigest.val
  publicEqual : storedPublic.val = publicDigest.val
  checksumEqual : storedChecksum.val = checksumDigest.val

theorem successful_resume_calls (ops : ResumeOps) {H : Type}
    (digestInst : aspis_core.digest.Digest32 H)
    (ne_sound : ∀ (s : Slice U8) (a : Array U8 32#usize),
      ops.ne core.cmp.PartialEqU8 s a = ok false → s.val = a.val)
    (bytes proof public1 : Slice U8) (v : transport.Variant) (hash : H)
    (p : verifier.Prepared) (acc : verifier.Accumulator)
    (success : verifier.resumeWithOps ops digestInst bytes proof public1 v hash =
      ok (.Ok (p,acc))) : Nonempty (Calls digestInst hash bytes proof public1) := by
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
  obtain ⟨hb, h⟩ := checkpoint_guard _ _ _ h
  obtain ⟨storedPublic, hsp, h⟩ := resume_bind_success _ _ _ h
  obtain ⟨publicParts, hpp, h⟩ := resume_bind_success _ _ _ h
  obtain ⟨publicDigest, hpd, h⟩ := resume_bind_success _ _ _ h
  obtain ⟨publicBad, hpb, h⟩ := resume_bind_success _ _ _ h
  obtain ⟨hpublicBad, h⟩ := checkpoint_guard _ _ _ h
  obtain ⟨storedChecksum, hsc, h⟩ := resume_bind_success _ _ _ h
  obtain ⟨domain, hdomain, h⟩ := resume_bind_success _ _ _ h
  obtain ⟨body, hbody, h⟩ := resume_bind_success _ _ _ h
  obtain ⟨checksumParts, hcp, h⟩ := resume_bind_success _ _ _ h
  obtain ⟨checksumDigest, hcd, h⟩ := resume_bind_success _ _ _ h
  obtain ⟨checksumBad, hcb, h⟩ := resume_bind_success _ _ _ h
  obtain ⟨hchecksumBad, _⟩ := checkpoint_guard _ _ _ h
  exact ⟨{ storedProof := stored, storedPublic := storedPublic, storedChecksum := storedChecksum,
            proofParts := chunks, publicParts := publicParts, checksumParts := checksumParts,
            proofDigest := digest, publicDigest := publicDigest, checksumDigest := checksumDigest, checksumEnd := end1,
            end_eq := hend, proofField := hstored, publicField := hsp, checksumField := hsc,
            proofInput := hchunks, publicInput := hpp, checksumDomain := domain,
            checksumBody := body, domainInput := hdomain, bodyInput := hbody,
            checksumInput := hcp, proofCall := hdigest, publicCall := hpd, checksumCall := hcd,
            proofEqual := ne_sound stored digest (hb ▸ hbad),
            publicEqual := ne_sound storedPublic publicDigest (hpublicBad ▸ hpb),
            checksumEqual := ne_sound storedChecksum checksumDigest (hchecksumBad ▸ hcb) }⟩

#print axioms resume_bind_success
#print axioms checkpoint_guard
#print axioms checkpoint_guard_prop
#print axioms successful_resume_calls
end AspisR1Stage2.Tx2ResumeDigests
