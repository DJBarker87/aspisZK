import EarlyPublicSelection
import R1UnifiedReseedCase
import R1UnifiedFramework

/-! Actual first-cell recovery of the public statement at the initial and
semantic-reseed rounds, reusing their existing sampler first-cell theorems. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.EarlyPublicSpecialCases

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open TranscriptView

variable {M Cv W : Type} {L : Nat}

theorem initial_first_cell (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (H : Addr L → State) (pub : UnifiedSampler.Public L) (pf : UnifiedProtocol.Proof M)
    (hpub : pub.pubBytes.length < 2^32) (htag : pub.tag = 2) (a : Addr L)
    (hfirst : firstCell ((UnifiedProtocol.protocol p hD extract).chain H pub pf 0) = some a) :
    EarlyPublicSelection.initial a = some pub := by
  have hi := UnifiedFramework.initial_firstCell p hD extract H pub pf.1 pf.2
  have ha : a = PublicInitFrame.addr pub.pubBytes pub.initFits pf.1 :=
    Option.some.inj (hfirst.symm.trans hi)
  rw [ha]
  exact EarlyPublicSelection.initial_addr pub pf.1 hpub htag

theorem reseed_first_cell (p : Params M Cv L) (hD : 5 ≤ p.D)
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
    (a : Addr L)
    (hfirst : firstCell ((UnifiedProtocol.protocol p hD extract).chain H pub
      (eval H prover).2 26) = some a) :
    let π := (eval H prover).2
    let tr := (eval H (FS.experiment prover
      (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1
    let T := tableBefore emptyTable tr a
    EarlyPublicSelection.ordinary p a T = some pub := by
  let π := (eval H prover).2
  let prior := (eval H prover).1
  let tr := (eval H (FS.experiment prover
    (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1
  have hcell := UnifiedReseedView.firstCell_eq p hD extract H pub π.1 π.2
  have ha : a = UnifiedSteps.address p hD H pub π.1 π.2 26 :=
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
    π.1 π.2 prior (FS.eval_consistent H prover) hpub htag hl he Qtot hQ hold 26 (by decide) (by decide)
  simpa only [htrace] using hsel

#print axioms initial_first_cell
#print axioms reseed_first_cell

end AspisR1.EarlyPublicSpecialCases
end
