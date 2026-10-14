import R1UnifiedOpeningInjection
import R1UnifiedOrdinaryFirstCell
import FS.LemmaB

/-! The opening-prefix decoder case on the actual prover/verifier experiment.
Ordinary-row first cells identify each of the four opening messages. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedOpeningCase

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open TranscriptView

variable {M Cv W : Type} {L : Nat}

theorem decodes_and_follows (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : UnifiedSampler.Prefix M Cv L → Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (prover : Program (Addr L) State (UnifiedProtocol.Proof M))
    (hpub : pub.pubBytes.length < 2^32)
    (hl : p.lbl 0 = 160)
    (he : p.enc ((eval H prover).2.2 0) = PublicInitFrame.emptyRecord)
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
    (k : Nat) (hk : k < 4) (a : Addr L)
    (hfirst : firstCell ((UnifiedProtocol.protocol p hD extract).chain H pub
      (eval H prover).2 (27 + k)) = some a) :
    let π := (eval H prover).2
    let tr := (eval H (FS.experiment prover
      (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1
    let T := tableBefore emptyTable tr a
    ∃ own pend g,
      UnifiedOpeningDecoder.decode p pub a T = some (own, pend, g) ∧
      bfollow g (traceFrom tr a) own pend T =
        some ((UnifiedProtocol.protocol p hD extract).transcript H pub π (27 + k),
          (UnifiedProtocol.protocol p hD extract).msg π (27 + k),
          (UnifiedProtocol.protocol p hD extract).chal H pub π (27 + k)) := by
  let π := (eval H prover).2
  let prior := (eval H prover).1
  let tr := (eval H (FS.experiment prover
    (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1
  have hcell := UnifiedOrdinaryFirstCell.firstCell_eq p hD extract H pub π.1 π.2
    (27 + k) (by omega) (by omega) (by omega)
  have ha : a = UnifiedSteps.address p hD H pub π.1 π.2 (27 + k) :=
    Option.some.inj (hfirst.symm.trans hcell)
  subst a
  have htrace : (eval H (FS.experiment prover
      (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1 =
      UnifiedPrefixedReads.trace p hD extract decision H pub π.1 π.2 prior := by
    dsimp [UnifiedPrefixedReads.trace, UnifiedTraceReads.trace,
      UnifiedVerifier.verifier]
    rw [FS.experiment_eval]
  rw [htrace] at hQ hold htail
  obtain ⟨own, pend, g, hdecode, hfollow⟩ :=
    UnifiedOpeningInjection.decodes_and_follows p hD extract decision H pub
      π.1 π.2 prior (FS.eval_consistent H prover) hpub hl he Qtot hQ hold htail k hk
  refine ⟨own, pend, g, ?_, ?_⟩
  · simpa only [htrace] using hdecode
  · have htrans := UnifiedProtocol.transcript_eq p hD extract H pub π (27 + k)
    have hmsg : (UnifiedProtocol.protocol p hD extract).msg π (27 + k) =
        UnifiedRun.message π.1 π.2 (27 + k) := rfl
    have hchal : (UnifiedProtocol.protocol p hD extract).chal H pub π (27 + k) =
        UnifiedRun.challenge p hD H pub π.1 π.2 (27 + k) := by
      rw [UnifiedProtocol.chal_eq]
      rfl
    rw [← htrans, ← hmsg, ← hchal] at hfollow
    simpa only [htrace] using hfollow

#print axioms decodes_and_follows

end AspisR1.UnifiedOpeningCase
end
