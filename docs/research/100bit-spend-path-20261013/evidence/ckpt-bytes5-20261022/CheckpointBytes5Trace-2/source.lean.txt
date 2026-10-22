import CheckpointBytes5Resume
import RawTx2ResumeDigestCalls
import OraclePortCkptAbiTry
set_option autoImplicit false
namespace AspisR1.CheckpointBytes5Trace
open Aeneas Aeneas.Std Result
open AspisR1Stage2 CheckpointBytes5Effect CheckpointBytes5Resume
open OraclePortCkptAbiTry (bind_success)

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
    ¬ b ∧ tail = ok (.Ok out) := by
  split at h
  · cases h
  · exact ⟨by assumption,h⟩

/-- The complete successful source schedule has exactly these three reads.
The pre-existing Calls inventory is now accompanied by an execution equation. -/
theorem successful_log (ops : ResumeOps) {H : Type}
    (digestInst : aspis_core.digest.Digest32 H)
    (ne_sound : ∀ (s : Slice U8) (a : Array U8 32#usize),
      ops.ne core.cmp.PartialEqU8 s a = ok false → s.val = a.val)
    (bytes proof public1 : Slice U8) (v : transport.Variant) (hash : H)
    (p : verifier.Prepared) (acc : verifier.Accumulator) (before : Log)
    (success : verifier.resumeWithOps ops digestInst bytes proof public1 v hash =
      ok (.Ok (p,acc))) : ∃ c : Tx2ResumeDigests.Calls digestInst hash bytes proof public1,
    run digestInst hash (program ops bytes proof public1 v) before =
      ok (.Ok (p,acc), before ++ [(c.proofParts,c.proofDigest),
        (c.publicParts,c.publicDigest),(c.checksumParts,c.checksumDigest)]) := by
  unfold verifier.resumeWithOps at success
  obtain ⟨size, hsize, h⟩ := bind_success _ _ _ success
  obtain ⟨hsizebad, h⟩ := checkpoint_guard _ _ _ h
  obtain ⟨header, hheader, h⟩ := bind_success _ _ _ h
  obtain ⟨magicBad, hmagic, h⟩ := bind_success _ _ _ h
  obtain ⟨hmagicbad, h⟩ := checkpoint_guard _ _ _ h
  obtain ⟨tagByte, htagbyte, h⟩ := bind_success _ _ _ h
  obtain ⟨tag, htag, h⟩ := bind_success _ _ _ h
  obtain ⟨htagbad, h⟩ := checkpoint_guard _ _ _ h
  obtain ⟨nextByte, hnext, h⟩ := bind_success _ _ _ h
  obtain ⟨hnextbad, h⟩ := checkpoint_guard_prop _ _ _ h
  obtain ⟨version, hversion, h⟩ := bind_success _ _ _ h
  obtain ⟨hversionbad, h⟩ := checkpoint_guard _ _ _ h
  obtain ⟨reserved, hreserved, h⟩ := bind_success _ _ _ h
  obtain ⟨iter, hiter, h⟩ := bind_success _ _ _ h
  obtain ⟨anyResult, hany, h⟩ := bind_success _ _ _ h
  rcases anyResult with ⟨anyBad, iterOut⟩
  obtain ⟨hanybad, h⟩ := checkpoint_guard _ _ _ h
  obtain ⟨end1, hend, h⟩ := bind_success _ _ _ h
  obtain ⟨stored, hstored, h⟩ := bind_success _ _ _ h
  obtain ⟨chunks, hchunks, h⟩ := bind_success _ _ _ h
  obtain ⟨digest, hdigest, h⟩ := bind_success _ _ _ h
  obtain ⟨bad, hbad, h⟩ := bind_success _ _ _ h
  obtain ⟨hb, h⟩ := checkpoint_guard _ _ _ h
  obtain ⟨storedPublic, hsp, h⟩ := bind_success _ _ _ h
  obtain ⟨publicParts, hpp, h⟩ := bind_success _ _ _ h
  obtain ⟨publicDigest, hpd, h⟩ := bind_success _ _ _ h
  obtain ⟨publicBad, hpb, h⟩ := bind_success _ _ _ h
  obtain ⟨hpublicBad, h⟩ := checkpoint_guard _ _ _ h
  obtain ⟨storedChecksum, hsc, h⟩ := bind_success _ _ _ h
  obtain ⟨domain, hdomain, h⟩ := bind_success _ _ _ h
  obtain ⟨body, hbody, h⟩ := bind_success _ _ _ h
  obtain ⟨checksumParts, hcp, h⟩ := bind_success _ _ _ h
  obtain ⟨checksumDigest, hcd, h⟩ := bind_success _ _ _ h
  have htail := h
  obtain ⟨checksumBad, hcb, h⟩ := bind_success _ _ _ h
  obtain ⟨hchecksumBad, _⟩ := checkpoint_guard _ _ _ h
  refine ⟨{ storedProof := stored, storedPublic := storedPublic, storedChecksum := storedChecksum,
            proofParts := chunks, publicParts := publicParts, checksumParts := checksumParts,
            proofDigest := digest, publicDigest := publicDigest, checksumDigest := checksumDigest, checksumEnd := end1,
            end_eq := hend, proofField := hstored, publicField := hsp, checksumField := hsc,
            proofInput := hchunks, publicInput := hpp, checksumDomain := domain,
            checksumBody := body, domainInput := hdomain, bodyInput := hbody,
            checksumInput := hcp, proofCall := hdigest, publicCall := hpd, checksumCall := hcd,
            proofEqual := ne_sound stored digest (hb ▸ hbad),
            publicEqual := ne_sound storedPublic publicDigest (hpublicBad ▸ hpb),
            checksumEqual := ne_sound storedChecksum checksumDigest (hchecksumBad ▸ hcb) }, ?_⟩

  simp only [program,run_bind,run_lift,run_read,run_pure,run_ite]
  simp only [Aeneas.Std.uncurry,hsize,bind_tc_ok,hsizebad,Bool.false_eq_true,if_false,
    hheader,hmagic,hmagicbad,htagbyte,htag,htagbad,hnext,if_neg hnextbad,
    hversion,hversionbad,hreserved,hiter,hany,hanybad,hend,hstored,hchunks,
    hdigest,hbad,hb,hsp,hpp,hpd,hpb,hpublicBad,hsc,hdomain,hbody,hcp,hcd]
  change (do let value ← tail ops bytes v nextByte end1 storedChecksum checksumDigest;
             ok (value,((before ++ [(chunks,digest)]) ++ [(publicParts,publicDigest)]) ++
                [(checksumParts,checksumDigest)])) = _
  have ht : tail ops bytes v nextByte end1 storedChecksum checksumDigest = ok (.Ok (p,acc)) := htail
  rw [ht]
  simp only [bind_tc_ok,List.append_assoc,List.cons_append,List.nil_append]

#print axioms checkpoint_guard
#print axioms checkpoint_guard_prop
#print axioms successful_log
end AspisR1.CheckpointBytes5Trace
