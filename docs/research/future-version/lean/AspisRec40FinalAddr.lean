import AspisRec40FollowProof
import AspisRec40FinalSelect
import AspisRows40FinalByte
import R1UnifiedPayloadZero

/-! Rows 33 to 39 at the address level, at R1's selected parameters: on the
40-row run after any consistent prior trace, the public statement is selected
at row n's frame, the final component decodes there, and its background output
followed along the trace is row n's actual prefix, message and challenge.

Copy of R1's `UnifiedTotalCase.decodes_and_follows` (with its payload-zero
canonicalisation `UnifiedPayloadZero`) for rows 33 to 39: the component is
`Final.component` (the lifted `Final.decode`), the context is W1
(`FinalContext.context_at`), the follow is `FollowProof.follow`, the selection
is W2 (`FinalSelect.select_at`, with R1's tag premise). The row-0 codec premise
of the follow (`p.enc (payload 0) = emptyRecord`) is met by replacing the unused
row-0 payload, which changes no trace, transcript, message or challenge. -/
set_option autoImplicit false
noncomputable section
namespace AspisRec40.FinalAddr
open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
open AspisR1 AspisR1.TranscriptView

abbrev M := SelectedTranscriptParams.Message
abbrev Cv := AspisWideTower.WideExact
abbrev L := SelectedTranscriptParams.L
abbrev p := SelectedTranscriptParams.params
theorem hD : 5 ≤ p.D := AspisRows40.FinalByte.hD

theorem lbl0 : p.lbl 0 = 160 := rfl

/-- The 40-row verifier trace does not read the row-0 payload. -/
theorem trace_payload_zero {W : Type}
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) → Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L) (c1 : State) (f : Nat → M) (m0 : M)
    (prior : List (Addr L × State)) :
    FinalRun.trace p hD extract decision H pub c1 (UnifiedPayloadZero.payload m0 f) prior =
      FinalRun.trace p hD extract decision H pub c1 f prior := by
  unfold FinalRun.trace FinalRun.verifier
  rw [FS2.verifier_eval, FS2.verifier_eval]
  have hc : ∀ i, (eval H ((FinalRun.protocol p hD extract).chain H pub
      (c1, UnifiedPayloadZero.payload m0 f) i).toProgram).1 =
      (eval H ((FinalRun.protocol p hD extract).chain H pub (c1, f) i).toProgram).1 := by
    intro i
    rw [FinalRun.chain_eq, FinalRun.chain_eq]
    change (eval H (UnifiedSampler.samp p hD i
        (UnifiedRun.transcript p hD H pub c1 (UnifiedPayloadZero.payload m0 f) i)
        (UnifiedRun.message c1 (UnifiedPayloadZero.payload m0 f) i)).toProgram).1 =
      (eval H (UnifiedSampler.samp p hD i (UnifiedRun.transcript p hD H pub c1 f i)
        (UnifiedRun.message c1 f i)).toProgram).1
    rw [UnifiedPayloadZero.transcript_eq, UnifiedPayloadZero.message_eq]
  simp only [hc]

/-- Address-level decoding and following of row n (33 ≤ n < 40), with the
row-0 codec premise. -/
theorem decodes_and_follows_codec {W : Type}
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) → Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L) (c1 : State) (payload : Nat → M)
    (prior : List (Addr L × State)) (hprior : ∀ q ∈ prior, q.2 = H q.1)
    (hpub : pub.pubBytes.length < 2^32) (htag : pub.tag = 2)
    (he : p.enc (payload 0) = PublicInitFrame.emptyRecord)
    (Qtot : Nat)
    (hQ : firstReads emptyTable (FinalRun.trace p hD extract decision H pub c1 payload prior) ≤ Qtot)
    (hold : ¬ hitsBad (badColl p Qtot) emptyTable
      (FinalRun.trace p hD extract decision H pub c1 payload prior))
    (htail : ¬ hitsBad (ParsedStateCollision.bad TrailingStateFrame.tailState Qtot) emptyTable
      (FinalRun.trace p hD extract decision H pub c1 payload prior))
    (n : Nat) (hlo : 33 ≤ n) (hhi : n < 40) :
    AspisRows40.FinalByte.select n (UnifiedSteps.address p hD H pub c1 payload n)
        (tableBefore emptyTable (FinalRun.trace p hD extract decision H pub c1 payload prior)
          (UnifiedSteps.address p hD H pub c1 payload n)) = some pub ∧
    ∃ own pend g,
      AspisRows40.Final.component p pub n (UnifiedSteps.address p hD H pub c1 payload n)
        (tableBefore emptyTable (FinalRun.trace p hD extract decision H pub c1 payload prior)
          (UnifiedSteps.address p hD H pub c1 payload n)) = some (own, pend, g) ∧
      bfollow g (traceFrom (FinalRun.trace p hD extract decision H pub c1 payload prior)
          (UnifiedSteps.address p hD H pub c1 payload n)) own pend
        (tableBefore emptyTable (FinalRun.trace p hD extract decision H pub c1 payload prior)
          (UnifiedSteps.address p hD H pub c1 payload n)) =
        some (UnifiedRun.transcript p hD H pub c1 payload n, UnifiedRun.message c1 payload n,
          UnifiedRun.challenge p hD H pub c1 payload n) := by
  refine ⟨FinalSelect.select_at hD extract decision H pub c1 payload prior hprior hpub htag
    lbl0 he Qtot hQ hold htail n hlo hhi, ?_⟩
  have hctx := FinalContext.context_at p hD extract decision H pub c1 payload prior hprior hpub
    lbl0 he Qtot hQ hold htail n hlo hhi
  have hdec := AspisRows40.Final.decode_of_parse p pub n _ _ _ hctx
  have hf := FollowProof.follow p hD extract decision H pub c1 payload prior hprior hpub lbl0 he
    Qtot hQ hold htail n hlo hhi
  refine ⟨_, _, _, DecoderStateList.lift_of_decode _ _ _ _ _ _ hdec, ?_⟩
  rw [DecoderStateList.lifted_follow]
  exact hf

/-- The same without the row-0 codec premise (payload-zero canonicalisation). -/
theorem decodes_and_follows {W : Type}
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) → Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L) (c1 : State) (payload : Nat → M)
    (prior : List (Addr L × State)) (hprior : ∀ q ∈ prior, q.2 = H q.1)
    (hpub : pub.pubBytes.length < 2^32) (htag : pub.tag = 2)
    (Qtot : Nat)
    (hQ : firstReads emptyTable (FinalRun.trace p hD extract decision H pub c1 payload prior) ≤ Qtot)
    (hold : ¬ hitsBad (badColl p Qtot) emptyTable
      (FinalRun.trace p hD extract decision H pub c1 payload prior))
    (htail : ¬ hitsBad (ParsedStateCollision.bad TrailingStateFrame.tailState Qtot) emptyTable
      (FinalRun.trace p hD extract decision H pub c1 payload prior))
    (n : Nat) (hlo : 33 ≤ n) (hhi : n < 40) :
    AspisRows40.FinalByte.select n (UnifiedSteps.address p hD H pub c1 payload n)
        (tableBefore emptyTable (FinalRun.trace p hD extract decision H pub c1 payload prior)
          (UnifiedSteps.address p hD H pub c1 payload n)) = some pub ∧
    ∃ own pend g,
      AspisRows40.Final.component p pub n (UnifiedSteps.address p hD H pub c1 payload n)
        (tableBefore emptyTable (FinalRun.trace p hD extract decision H pub c1 payload prior)
          (UnifiedSteps.address p hD H pub c1 payload n)) = some (own, pend, g) ∧
      bfollow g (traceFrom (FinalRun.trace p hD extract decision H pub c1 payload prior)
          (UnifiedSteps.address p hD H pub c1 payload n)) own pend
        (tableBefore emptyTable (FinalRun.trace p hD extract decision H pub c1 payload prior)
          (UnifiedSteps.address p hD H pub c1 payload n)) =
        some (UnifiedRun.transcript p hD H pub c1 payload n, UnifiedRun.message c1 payload n,
          UnifiedRun.challenge p hD H pub c1 payload n) := by
  let m0 : M := ⟨PublicInitFrame.emptyRecord, by decide⟩
  let f := UnifiedPayloadZero.payload m0 payload
  have htr := trace_payload_zero extract decision H pub c1 payload m0 prior
  have haddr : UnifiedSteps.address p hD H pub c1 f n =
      UnifiedSteps.address p hD H pub c1 payload n := by
    unfold UnifiedSteps.address
    have hprev : UnifiedRecords.previous p hD H pub c1 f n =
        UnifiedRecords.previous p hD H pub c1 payload n := by
      obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
      exact UnifiedPayloadZero.state_eq p hD H pub c1 m0 payload (j + 1)
    have hfn : f n = payload n := UnifiedPayloadZero.payload_ne_zero m0 payload (by omega : n ≠ 0)
    rw [hprev]
    congr 2
  have he : p.enc (f 0) = PublicInitFrame.emptyRecord := by
    show p.enc (UnifiedPayloadZero.payload m0 payload 0) = _
    rw [UnifiedPayloadZero.payload_zero]; rfl
  have h := decodes_and_follows_codec extract decision H pub c1 f prior hprior hpub htag he Qtot
    (by rw [htr]; exact hQ) (by rw [htr]; exact hold) (by rw [htr]; exact htail) n hlo hhi
  rw [htr, haddr, UnifiedPayloadZero.transcript_eq, UnifiedPayloadZero.message_eq,
    UnifiedPayloadZero.challenge_eq] at h
  exact h

#print axioms lbl0
#print axioms trace_payload_zero
#print axioms decodes_and_follows_codec
#print axioms decodes_and_follows

end AspisRec40.FinalAddr
end
