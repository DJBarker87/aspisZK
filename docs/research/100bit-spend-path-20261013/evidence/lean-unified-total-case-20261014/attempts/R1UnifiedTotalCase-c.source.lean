import R1UnifiedDispatchCase
import R1UnifiedCanonicalProver

/-! Transfer the complete row dispatcher from the canonical empty row-zero
payload to an arbitrary prover, preserving its experiment trace. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedTotalCase

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1.TranscriptView

variable {M Cv W : Type} {L : Nat}

theorem decodes_and_follows (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : UnifiedSampler.Prefix M Cv L → Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (prover : Program (Addr L) State (UnifiedProtocol.Proof M))
    (hpub : pub.pubBytes.length < 2^32)
    (hl : ∀ n < 33, p.lbl n = UnifiedLabels.label n)
    (m0 : M) (he0 : p.enc m0 = PublicInitFrame.emptyRecord)
    (Qtot : Nat)
    (hQ : firstReads emptyTable
      (eval H (FS.experiment prover
        (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1 ≤ Qtot)
    (hold : ¬ hitsBad (badColl p Qtot) emptyTable
      (eval H (FS.experiment prover
        (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1)
    (htail : ¬ hitsBad (ParsedStateCollision.bad TrailingStateFrame.tailState Qtot)
      emptyTable (eval H (FS.experiment prover
        (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1)
    (n : Nat) (hn : n < 33) (a : Addr L)
    (hfirst : firstCell ((UnifiedProtocol.protocol p hD extract).chain H pub
      (eval H prover).2 n) = some a) :
    let π := (eval H prover).2
    let tr := (eval H (FS.experiment prover
      (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1
    let T := tableBefore emptyTable tr a
    ∃ own pend g,
      UnifiedDecoder.decode p hD pub a T = some (own, pend, g) ∧
      bfollow g (traceFrom tr a) own pend T =
        some ((UnifiedProtocol.protocol p hD extract).transcript H pub π n,
          (UnifiedProtocol.protocol p hD extract).msg π n,
          (UnifiedProtocol.protocol p hD extract).chal H pub π n) := by
  dsimp only
  let canon := UnifiedCanonicalProver.prover m0 prover
  have htrace :
      (eval H (FS.experiment canon
        (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1 =
      (eval H (FS.experiment prover
        (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1 := by
    rw [FS.experiment_eval, FS.experiment_eval, UnifiedCanonicalProver.eval_prover]
    rw [UnifiedPayloadZero.verifier_eq p hD extract decision pub (eval H prover).2 m0]
  have hQcanon : firstReads emptyTable
      (eval H (FS.experiment canon
        (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1 ≤ Qtot := by
    rw [htrace]
    exact hQ
  have holdcanon : ¬ hitsBad (badColl p Qtot) emptyTable
      (eval H (FS.experiment canon
        (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1 := by
    rw [htrace]
    exact hold
  have htailcanon : ¬ hitsBad (ParsedStateCollision.bad TrailingStateFrame.tailState Qtot)
      emptyTable (eval H (FS.experiment canon
        (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1 := by
    rw [htrace]
    exact htail
  have hfirstcanon : firstCell ((UnifiedProtocol.protocol p hD extract).chain H pub
      (eval H canon).2 n) = some a := by
    change firstCell ((UnifiedProtocol.protocol p hD extract).chain H pub
      (eval H (UnifiedCanonicalProver.prover m0 prover)).2 n) = some a
    rw [UnifiedCanonicalProver.eval_prover]
    rw [UnifiedPayloadZero.protocol_chain_eq p hD extract H pub
      (eval H prover).2 m0 n]
    exact hfirst
  have hcodec := UnifiedCanonicalProver.codec p H m0 prover he0
  have hpicanon : (eval H canon).2 =
      UnifiedPayloadZero.proof m0 (eval H prover).2 := by
    dsimp [canon]
    rw [UnifiedCanonicalProver.eval_prover]
  obtain ⟨own, pend, g, hdecode, hfollow⟩ :=
    UnifiedDispatchCase.decodes_and_follows p hD extract decision H pub canon
      hpub hl hcodec Qtot hQcanon holdcanon htailcanon n hn a hfirstcanon
  refine ⟨own, pend, g, ?_, ?_⟩
  · rw [htrace] at hdecode
    exact hdecode
  · have htrans := UnifiedPayloadZero.protocol_transcript_eq p hD extract H pub
      (eval H prover).2 m0 n
    have hmsg := UnifiedPayloadZero.protocol_message_eq p hD extract
      (eval H prover).2 m0 n
    have hchal := UnifiedPayloadZero.protocol_challenge_eq p hD extract H pub
      (eval H prover).2 m0 n
    rw [htrace] at hfollow
    rw [hpicanon, htrans, hmsg, hchal] at hfollow
    exact hfollow

#print axioms decodes_and_follows

end AspisR1.UnifiedTotalCase
end
