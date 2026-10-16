import FullPublicSelection
import RawPublicOpeningRecovery
import R1UnifiedOrdinaryFirstCell
import R1UnifiedQueryView

/-! The public-free dispatch selector succeeds on actual bounded prover
experiments for the four opening rows and query row 31. The row-zero codec
premise is explicit here; canonical-prover transport is applied separately. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.FullPublicOpeningCase
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open TranscriptView
variable {M Cv W : Type} {L : Nat}

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
      (eval H (FS.experiment prover
        (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1 ≤ Qtot)
    (hold : ¬ hitsBad (badColl p Qtot) emptyTable
      (eval H (FS.experiment prover
        (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1)
    (htail : ¬ hitsBad (ParsedStateCollision.bad TrailingStateFrame.tailState Qtot)
      emptyTable (eval H (FS.experiment prover
        (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1)
    (k : Nat) (hk : k ≤ 4) (a : Addr L)
    (hfirst : firstCell ((UnifiedProtocol.protocol p hD extract).chain H pub
      (eval H prover).2 (27 + k)) = some a) :
    FullPublicSelection.select p a (tableBefore emptyTable
      (eval H (FS.experiment prover
        (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1 a) = some pub := by
  let π := (eval H prover).2
  let prior := (eval H prover).1
  have hcell : firstCell ((UnifiedProtocol.protocol p hD extract).chain H pub π (27 + k)) =
      some (UnifiedSteps.address p hD H pub π.1 π.2 (27 + k)) := by
    by_cases hk4 : k = 4
    · subst k
      exact UnifiedQueryView.firstCell_eq p hD extract H pub π.1 π.2
    · exact UnifiedOrdinaryFirstCell.firstCell_eq p hD extract H pub π.1 π.2
        (27 + k) (by omega) (by omega) (by omega)
  have ha : a = UnifiedSteps.address p hD H pub π.1 π.2 (27 + k) :=
    Option.some.inj (hfirst.symm.trans hcell)
  subst a
  have htrace : (eval H (FS.experiment prover
      (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1 =
      UnifiedPrefixedReads.trace p hD extract decision H pub π.1 π.2 prior := by
    dsimp [UnifiedPrefixedReads.trace, UnifiedTraceReads.trace, UnifiedVerifier.verifier]
    rw [FS.experiment_eval]
  rw [htrace] at hQ hold htail ⊢
  have hs := RawPublicOpeningRecovery.select_before_row p hD extract decision H pub
    π.1 π.2 prior (FS.eval_consistent H prover) hpub htag hl he Qtot hQ hold htail k hk
  dsimp only at hs
  rw [htag,UnifiedPhases.opening_previous] at hs
  unfold UnifiedSteps.address
  rw [FullPublicSelection.opening p _ _ _ _ (27+k) (by omega) (by omega)
    (hlabels (27+k) (by omega))]
  exact hs

#print axioms canonical_first_cell
end AspisR1.FullPublicOpeningCase
end
