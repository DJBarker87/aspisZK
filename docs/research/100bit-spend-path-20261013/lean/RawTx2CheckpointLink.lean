import RawTx2DigestLog

/-! Shared-oracle composition. Neither checkpoint digest equality alone nor
separate per-transaction consistency implies a common oracle law. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1Stage2.Tx2CheckpointLink
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisR1DigestLogCarrier

/-- Exactly the stored-field part still needed from the parked writer plus
runtime checkpoint provenance. It is a named premise, not an imported theorem
about the frozen writer. Proof and public fields are separate. -/
structure WriterStoredDigestFields (bytes : Slice U8)
    (proofDigest publicDigest : Array U8 32#usize) : Prop where
  proofField : ∀ stored : Slice U8,
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      bytes {start := 16#usize, «end» := 48#usize} = ok stored →
      stored.val = proofDigest.val
  publicField : ∀ stored : Slice U8,
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      bytes {start := 48#usize, «end» := 80#usize} = ok stored →
      stored.val = publicDigest.val

/-- Matches the parked writer/resume singleton-input agreement, expressed
without importing its changed verifier source. Frozen writer discharge is owed. -/
def ParkedWriterResumeProofAgreement {H : Type}
    (D : aspis_core.digest.Digest32 H) (hash : H) (proof : Slice U8)
    (writerProofDigest : Array U8 32#usize) : Prop :=
  ∃ chunks : Slice (Slice U8),
    lift (Array.to_slice (Array.make 1#usize [proof])) = ok chunks ∧
    D.digest hash chunks = ok writerProofDigest

theorem checkpoint_digest_link {H : Type} {D : aspis_core.digest.Digest32 H}
    {hash : H} {bytes proof public1 : Slice U8}
    (calls : Tx2ResumeDigests.Calls D hash bytes proof public1)
    (writerProofDigest writerPublicDigest : Array U8 32#usize)
    (writerFields : WriterStoredDigestFields bytes writerProofDigest writerPublicDigest) :
    calls.proofDigest.val = writerProofDigest.val ∧
      calls.publicDigest.val = writerPublicDigest.val := by
  exact ⟨calls.proofEqual.symm.trans (writerFields.proofField _ calls.proofField),
    calls.publicEqual.symm.trans (writerFields.publicField _ calls.publicField)⟩

/-- Determinism of the same dictionary/hash/singleton input suffices for the
parked proof-digest agreement. No collision assumption is used in this direction. -/
theorem parked_proof_agreement {H : Type} {D : aspis_core.digest.Digest32 H}
    {hash : H} {bytes proof public1 : Slice U8}
    (calls : Tx2ResumeDigests.Calls D hash bytes proof public1)
    (writerDigest : Array U8 32#usize)
    (parked : ParkedWriterResumeProofAgreement D hash proof writerDigest) :
    calls.proofDigest = writerDigest := by
  obtain ⟨chunks,hchunks,hdigest⟩ := parked
  have hinput : chunks = calls.proofParts := Result.ok.inj (hchunks.symm.trans calls.proofInput)
  subst chunks
  exact Result.ok.inj (calls.proofCall.symm.trans hdigest)

/-- Existing stage-2 checkpoint fact is genuinely consumed: success alone
supplies the proof field/call; stored-field provenance remains named. -/
theorem successful_resume_proof_link (ops : ResumeOps) {H : Type}
    (D : aspis_core.digest.Digest32 H)
    (ne_sound : ∀ (s : Slice U8) (a : Array U8 32#usize),
      ops.ne core.cmp.PartialEqU8 s a = ok false → s.val = a.val)
    (bytes proof public1 : Slice U8) (v : transport.Variant) (hash : H)
    (p : verifier.Prepared) (acc : verifier.Accumulator)
    (writerProofDigest writerPublicDigest : Array U8 32#usize)
    (writerFields : WriterStoredDigestFields bytes writerProofDigest writerPublicDigest)
    (success : verifier.resumeWithOps ops D bytes proof public1 v hash = ok (.Ok (p,acc))) :
    ∃ chunks digest,
      lift (Array.to_slice (Array.make 1#usize [proof])) = ok chunks ∧
      D.digest hash chunks = ok digest ∧ digest.val = writerProofDigest.val := by
  obtain ⟨stored,chunks,digest,hfield,hinput,hcall,heq⟩ :=
    resume_rehash_checkpoint_field ops D ne_sound bytes proof public1 v hash p acc success
  exact ⟨chunks,digest,hinput,hcall,heq.symm.trans (writerFields.proofField stored hfield)⟩

#print axioms checkpoint_digest_link
#print axioms parked_proof_agreement
#print axioms successful_resume_proof_link
end AspisR1Stage2.Tx2CheckpointLink
end
