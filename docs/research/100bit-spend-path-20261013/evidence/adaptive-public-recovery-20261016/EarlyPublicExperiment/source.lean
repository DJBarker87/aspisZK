import EarlyPublicSelection
import R1UnifiedSemanticCase
import R1UnifiedFramework

/-! Public recovery on actual bounded-model experiments. The selected first
cell and consistent prior trace are derived from the existing run model. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.EarlyPublicExperiment

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open TranscriptView

variable {M Cv W : Type} {L : Nat}

theorem ordinary_at_first_cell (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : UnifiedSampler.Prefix M Cv L → Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (prover : Program (Addr L) State (UnifiedProtocol.Proof M))
    (hpub : pub.pubBytes.length < 2^32) (htag : pub.tag = 2)
    (hl : p.lbl 0 = 160)
    (he : p.enc ((eval H prover).2.2 0) = PublicInitFrame.emptyRecord)
    (Qtot : Nat)
    (hQ : firstReads emptyTable
      (eval H (FS.experiment prover
        (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1 ≤ Qtot)
    (hold : ¬ hitsBad (badColl p Qtot) emptyTable
      (eval H (FS.experiment prover
        (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1)
    (n : Nat) (hn : 0 < n) (hn26 : n < 26)
    (a : Addr L)
    (hfirst : firstCell ((UnifiedProtocol.protocol p hD extract).chain H pub
      (eval H prover).2 n) = some a) :
    let π := (eval H prover).2
    let tr := (eval H (FS.experiment prover
      (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1
    let T := tableBefore emptyTable tr a
    EarlyPublicSelection.ordinary p a T = some pub := by
  let π := (eval H prover).2
  let prior := (eval H prover).1
  let tr := (eval H (FS.experiment prover
    (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1
  have hcell := UnifiedOrdinaryFirstCell.firstCell_eq p hD extract H pub π.1 π.2 n
    (by omega) (by omega) (by omega)
  have ha : a = UnifiedSteps.address p hD H pub π.1 π.2 n :=
    Option.some.inj (hfirst.symm.trans hcell)
  subst a
  have htrace : (eval H (FS.experiment prover
      (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1 =
      UnifiedPrefixedReads.trace p hD extract decision H pub π.1 π.2 prior := by
    dsimp [UnifiedPrefixedReads.trace, UnifiedTraceReads.trace,
      UnifiedVerifier.verifier]
    rw [FS.experiment_eval]
  rw [htrace] at hQ hold
  have hsel := EarlyPublicSelection.ordinary_before_row p hD extract decision H pub
    π.1 π.2 prior (FS.eval_consistent H prover) hpub htag hl he Qtot hQ hold n hn (by omega)
  simpa only [htrace] using hsel

#print axioms ordinary_at_first_cell

end AspisR1.EarlyPublicExperiment
end
