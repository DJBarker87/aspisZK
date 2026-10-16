import FullPublicSelection
import EarlyPublicTotalCase

/-! The unified dispatch selector recovers the actual statement at every
early row, reusing the checked early selector and its canonical-row-zero
transport. Only the concrete label schedule is added. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.FullPublicEarlyCase
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open TranscriptView
variable {M Cv W : Type} {L : Nat}

theorem actual_first_cell (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : UnifiedSampler.Prefix M Cv L → Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (prover : Program (Addr L) State (UnifiedProtocol.Proof M))
    (hpub : pub.pubBytes.length < 2^32) (htag : pub.tag = 2)
    (hlabels : ∀ i < 33, p.lbl i = UnifiedLabels.label i)
    (hl : p.lbl 0 = 160) (m0 : M) (he0 : p.enc m0 = PublicInitFrame.emptyRecord)
    (Q : Nat)
    (hQ : firstReads emptyTable (eval H (FS.experiment prover
      (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1 ≤ Q)
    (hout : ¬ hitsBad (badColl p Q) emptyTable (eval H (FS.experiment prover
      (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1)
    (n : Nat) (hn : n ≤ 26) (a : Addr L)
    (hfirst : firstCell ((UnifiedProtocol.protocol p hD extract).chain H pub (eval H prover).2 n) = some a) :
    FullPublicSelection.select p a (tableBefore emptyTable (eval H (FS.experiment prover
      (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1 a) = some pub := by
  have hs := EarlyPublicTotalCase.actual_first_cell p hD extract decision H pub prover
    hpub htag hl m0 he0 Q hQ hout n hn a hfirst
  by_cases h0 : n = 0
  · subst n
    have hi := UnifiedFramework.initial_firstCell p hD extract H pub
      (eval H prover).2.1 (eval H prover).2.2
    have ha : a = PublicInitFrame.addr pub.pubBytes pub.initFits (eval H prover).2.1 :=
      Option.some.inj (hfirst.symm.trans hi)
    rw [ha]
    exact FullPublicSelection.initial p pub _ hpub htag _
  · have ha : a = UnifiedSteps.address p hD H pub (eval H prover).2.1 (eval H prover).2.2 n := by
      by_cases h26 : n = 26
      · subst n
        exact Option.some.inj (hfirst.symm.trans
          (UnifiedReseedView.firstCell_eq p hD extract H pub (eval H prover).2.1 (eval H prover).2.2))
      · exact Option.some.inj (hfirst.symm.trans
          (UnifiedOrdinaryFirstCell.firstCell_eq p hD extract H pub
            (eval H prover).2.1 (eval H prover).2.2 n h0 h26 (by omega)))
    subst a
    unfold UnifiedSteps.address
    rw [FullPublicSelection.early p _ _ _ _ n hn (hlabels n (by omega))]
    simpa [EarlyPublicTotalCase.select,EarlyPublicSelection.initial,UnifiedSteps.address,
      RawPublicInitParser.parse_absorb_none] using hs

#print axioms actual_first_cell
end AspisR1.FullPublicEarlyCase
end
