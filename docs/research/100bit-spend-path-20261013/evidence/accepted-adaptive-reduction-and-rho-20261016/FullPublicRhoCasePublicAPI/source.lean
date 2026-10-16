import RawPublicRhoRecovery
import R1UnifiedOrdinaryFirstCell
import R1UnifiedPrefixedReads

/-! Tiny bounded experiment wrapper around the public-free row-32 rho lemma. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.FullPublicRhoCaseWrapper

open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open TranscriptView

variable {M Cv W : Type} {L : Nat}
attribute [local irreducible] FullPublicSelection.select UnifiedProtocol.protocol

@[irreducible] def rowChain (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (π : UnifiedProtocol.Proof M) (i : Nat) :=
  (UnifiedProtocol.protocol p hD extract).chain H pub π i

@[irreducible] def experimentTrace (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : UnifiedSampler.Prefix M Cv L → Message M → Bool)
    (H : Addr L → State) (prover : Program (Addr L) State (UnifiedProtocol.Proof M))
    (pub : UnifiedSampler.Public L) : List (Addr L × State) :=
  (eval H (FS.experiment prover
    (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1

theorem experimentTrace_eq (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : UnifiedSampler.Prefix M Cv L → Message M → Bool)
    (H : Addr L → State) (prover : Program (Addr L) State (UnifiedProtocol.Proof M))
    (pub : UnifiedSampler.Public L) :
    experimentTrace p hD extract decision H prover pub =
      (eval H (FS.experiment prover
        (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1 := by
  unfold experimentTrace
  rfl

theorem rowChain_eq (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (π : UnifiedProtocol.Proof M) (i : Nat) :
    rowChain p hD extract H pub π i =
      (UnifiedProtocol.protocol p hD extract).chain H pub π i := by
  unfold rowChain
  rfl

theorem canonical_first_cell (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : UnifiedSampler.Prefix M Cv L → Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (prover : Program (Addr L) State (UnifiedProtocol.Proof M))
    (hpub : pub.pubBytes.length < 2^32) (htag : pub.tag = 2)
    (hlabels : ∀ i < 33, p.lbl i = UnifiedLabels.label i)
    (hl : p.lbl 0 = 160)
    (he : p.enc ((eval H prover).2.2 0) = PublicInitFrame.emptyRecord)
    (Qtot : Nat)
    (hQ : firstReads emptyTable
      (experimentTrace p hD extract decision H prover pub) ≤ Qtot)
    (hold : ¬ hitsBad (badColl p Qtot) emptyTable
      (experimentTrace p hD extract decision H prover pub))
    (htail : ¬ hitsBad (ParsedStateCollision.bad TrailingStateFrame.tailState Qtot)
      emptyTable (experimentTrace p hD extract decision H prover pub))
    (a : Addr L) (Tout : Table (Addr L) State)
    (hT : Tout = tableBefore emptyTable (experimentTrace p hD extract decision H prover pub) a)
    (hfirst : firstCell (rowChain p hD extract H pub (eval H prover).2 32) = some a) :
    FullPublicSelection.select p a Tout = some pub := by
  let π := (eval H prover).2
  let prior := (eval H prover).1
  have hcell : firstCell ((UnifiedProtocol.protocol p hD extract).chain H pub π 32) =
      some (UnifiedSteps.address p hD H pub π.1 π.2 32) :=
    UnifiedOrdinaryFirstCell.firstCell_eq p hD extract H pub π.1 π.2 32
      (by decide) (by decide) (by decide)
  have hfirst' : firstCell ((UnifiedProtocol.protocol p hD extract).chain H pub π 32) = some a := by
    simpa [rowChain] using hfirst
  have ha : a = UnifiedSteps.address p hD H pub π.1 π.2 32 :=
    Option.some.inj (hfirst'.symm.trans hcell)
  subst a
  have htrace : experimentTrace p hD extract decision H prover pub =
      UnifiedPrefixedReads.trace p hD extract decision H pub π.1 π.2 prior := by
    unfold experimentTrace
    dsimp [UnifiedPrefixedReads.trace, UnifiedTraceReads.trace, UnifiedVerifier.verifier]
    rw [FS.experiment_eval]
  rw [htrace] at hQ hold htail hT
  let tr := UnifiedPrefixedReads.trace p hD extract decision H pub π.1 π.2 prior
  let c := UnifiedQueryRun.rhoAddress p hD H pub π.1 π.2
  have hcurrent : c = UnifiedSteps.address p hD H pub π.1 π.2 32 :=
    UnifiedSteps.payload_address p hD H pub π.1 π.2 32 (by decide)
  have htable : Tout = tableBefore emptyTable tr c := by
    rw [hcurrent]
    exact hT
  have hselected := RawPublicRhoRecovery.select_before_rho p hD extract decision H pub
    π.1 π.2 prior (FS.eval_consistent H prover) hpub htag hlabels hl he Qtot hQ hold htail
    Tout htable
  rw [← hcurrent]
  exact hselected

theorem canonical_first_cell_actual (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : UnifiedSampler.Prefix M Cv L → Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (prover : Program (Addr L) State (UnifiedProtocol.Proof M))
    (hpub : pub.pubBytes.length < 2^32) (htag : pub.tag = 2)
    (hlabels : ∀ i < 33, p.lbl i = UnifiedLabels.label i)
    (hl : p.lbl 0 = 160)
    (he : p.enc ((eval H prover).2.2 0) = PublicInitFrame.emptyRecord)
    (Qtot : Nat)
    (hQ : firstReads emptyTable
      ((eval H (FS.experiment prover
        (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1) ≤ Qtot)
    (hold : ¬ hitsBad (badColl p Qtot) emptyTable
      ((eval H (FS.experiment prover
        (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1))
    (htail : ¬ hitsBad (ParsedStateCollision.bad TrailingStateFrame.tailState Qtot)
      emptyTable ((eval H (FS.experiment prover
        (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1))
    (a : Addr L)
    (hfirst : firstCell ((UnifiedProtocol.protocol p hD extract).chain H pub
      (eval H prover).2 32) = some a) :
    FullPublicSelection.select p a
      (tableBefore emptyTable
        ((eval H (FS.experiment prover
          (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1) a) = some pub := by
  let tout := tableBefore emptyTable
    ((eval H (FS.experiment prover
      (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1) a
  have hQ' : firstReads emptyTable (experimentTrace p hD extract decision H prover pub) ≤ Qtot := by
    rw [experimentTrace_eq]
    exact hQ
  have hold' : ¬ hitsBad (badColl p Qtot) emptyTable
      (experimentTrace p hD extract decision H prover pub) := by
    rw [experimentTrace_eq]
    exact hold
  have htail' : ¬ hitsBad (ParsedStateCollision.bad TrailingStateFrame.tailState Qtot)
      emptyTable (experimentTrace p hD extract decision H prover pub) := by
    rw [experimentTrace_eq]
    exact htail
  have hfirst' : firstCell (rowChain p hD extract H pub (eval H prover).2 32) = some a := by
    rw [rowChain_eq]
    exact hfirst
  have hT' : tout = tableBefore emptyTable (experimentTrace p hD extract decision H prover pub) a := by
    rw [experimentTrace_eq]
  have hresult := canonical_first_cell p hD extract decision H pub prover hpub htag
    hlabels hl he Qtot hQ' hold' htail' a tout hT' hfirst'
  simpa [tout, experimentTrace_eq] using hresult

#print axioms AspisR1.FullPublicRhoCaseWrapper.experimentTrace_eq
#print axioms AspisR1.FullPublicRhoCaseWrapper.rowChain_eq
#print axioms AspisR1.FullPublicRhoCaseWrapper.canonical_first_cell_actual

end AspisR1.FullPublicRhoCaseWrapper
end
