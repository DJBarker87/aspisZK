import R1UnifiedRhoInjection
import FS.LemmaB

/-! Apply the rho-case decoder bridge to the actual prover-then-verifier
experiment. Consistency of the prover's prior trace is discharged by the
generic evaluator theorem; all budget and collision hypotheses remain on the
actual experiment trace. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedExperimentInjection

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
        (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1) :
    let π := (eval H prover).2
    let tr := (eval H (FS.experiment prover
      (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1
    let c := UnifiedQueryRun.rhoAddress p hD H pub π.1 π.2
    let T := tableBefore emptyTable tr c
    ∃ own pend g,
      JointUnifiedDecoder.decode p pub 27 4 c T = some (own, pend, g) ∧
      bfollow g (traceFrom tr c) own pend T =
        some (UnifiedRun.transcript p hD H pub π.1 π.2 32,
          UnifiedRun.message π.1 π.2 32,
          UnifiedRun.challenge p hD H pub π.1 π.2 32) := by
  let π := (eval H prover).2
  let prior := (eval H prover).1
  have htrace : (eval H (FS.experiment prover
      (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1 =
      UnifiedPrefixedReads.trace p hD extract decision H pub π.1 π.2 prior := by
    dsimp [UnifiedPrefixedReads.trace, UnifiedTraceReads.trace,
      UnifiedVerifier.verifier]
    rw [FS.experiment_eval]
  rw [htrace] at hQ hold htail
  simpa only [htrace] using UnifiedRhoInjection.decodes_and_follows p hD extract
    decision H pub π.1 π.2 prior (FS.eval_consistent H prover) hpub hl he Qtot hQ hold htail

#print axioms decodes_and_follows

end AspisR1.UnifiedExperimentInjection
end
