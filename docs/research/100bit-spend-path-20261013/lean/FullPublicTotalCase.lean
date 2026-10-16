import FullPublicEarlyCase
import FullPublicOpeningCase
import FullPublicRhoCasePublicAPI
import R1UnifiedCanonicalProver

/-! All-33-round public-free selection on the actual bounded prover experiment.
The checked early, opening and final-query cases are joined and existing
canonical-row-zero transport removes the dummy-payload condition. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.FullPublicTotalCase
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open TranscriptView
variable {M Cv W : Type} {L : Nat}

theorem canonical_case (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : UnifiedSampler.Prefix M Cv L → Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (prover : Program (Addr L) State (UnifiedProtocol.Proof M))
    (hpub : pub.pubBytes.length < 2^32) (htag : pub.tag = 2)
    (hlabels : ∀ i < 33, p.lbl i = UnifiedLabels.label i)
    (hl : p.lbl 0 = 160) (he : p.enc ((eval H prover).2.2 0) = PublicInitFrame.emptyRecord)
    (Q : Nat)
    (hQ : firstReads emptyTable (eval H (FS.experiment prover
      (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1 ≤ Q)
    (hout : ¬ hitsBad (badColl p Q) emptyTable (eval H (FS.experiment prover
      (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1)
    (htail : ¬ hitsBad (ParsedStateCollision.bad TrailingStateFrame.tailState Q) emptyTable
      (eval H (FS.experiment prover
        (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1)
    (n : Nat) (hn : n < 33) (a : Addr L)
    (hfirst : firstCell ((UnifiedProtocol.protocol p hD extract).chain H pub (eval H prover).2 n) = some a) :
    FullPublicSelection.select p a (tableBefore emptyTable (eval H (FS.experiment prover
      (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1 a) = some pub := by
  by_cases hearly : n ≤ 26
  · exact FullPublicEarlyCase.actual_first_cell p hD extract decision H pub prover
      hpub htag hlabels hl ((eval H prover).2.2 0) he Q hQ hout n hearly a hfirst
  · by_cases hopen : n ≤ 31
    · have heq : n = 27 + (n - 27) := by omega
      rw [heq] at hfirst
      exact FullPublicOpeningCase.canonical_first_cell p hD extract decision H pub prover
        hpub htag hlabels hl he Q hQ hout htail (n-27) (by omega) a hfirst
    · have heq : n = 32 := by omega
      subst n
      exact FullPublicRhoCaseWrapper.canonical_first_cell_actual p hD extract decision H pub prover
        hpub htag hlabels hl he Q hQ hout htail a hfirst

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
    (htail : ¬ hitsBad (ParsedStateCollision.bad TrailingStateFrame.tailState Q) emptyTable
      (eval H (FS.experiment prover
        (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1)
    (n : Nat) (hn : n < 33) (a : Addr L)
    (hfirst : firstCell ((UnifiedProtocol.protocol p hD extract).chain H pub (eval H prover).2 n) = some a) :
    FullPublicSelection.select p a (tableBefore emptyTable (eval H (FS.experiment prover
      (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1 a) = some pub := by
  let canon := UnifiedCanonicalProver.prover m0 prover
  have htrace : (eval H (FS.experiment canon
      (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1 =
      (eval H (FS.experiment prover
        (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1 := by
    rw [FS.experiment_eval, FS.experiment_eval, UnifiedCanonicalProver.eval_prover]
    rw [UnifiedPayloadZero.verifier_eq p hD extract decision pub (eval H prover).2 m0]
  have hfirstCanon : firstCell ((UnifiedProtocol.protocol p hD extract).chain H pub
      (eval H canon).2 n) = some a := by
    change firstCell ((UnifiedProtocol.protocol p hD extract).chain H pub
      (eval H (UnifiedCanonicalProver.prover m0 prover)).2 n) = some a
    rw [UnifiedCanonicalProver.eval_prover,UnifiedPayloadZero.protocol_chain_eq]
    exact hfirst
  have hqc : firstReads emptyTable (eval H (FS.experiment canon
      (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1 ≤ Q := by
    rw [htrace]
    exact hQ
  have hoc : ¬ hitsBad (badColl p Q) emptyTable (eval H (FS.experiment canon
      (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1 := by
    rw [htrace]
    exact hout
  have htc : ¬ hitsBad (ParsedStateCollision.bad TrailingStateFrame.tailState Q) emptyTable
      (eval H (FS.experiment canon
        (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1 := by
    rw [htrace]
    exact htail
  have hc := canonical_case p hD extract decision H pub canon hpub htag hlabels hl
    (UnifiedCanonicalProver.codec p H m0 prover he0) Q hqc hoc htc n hn a hfirstCanon
  rw [htrace] at hc
  exact hc

#print axioms canonical_case
#print axioms actual_first_cell
end AspisR1.FullPublicTotalCase
end
