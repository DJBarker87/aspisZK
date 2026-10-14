import R1UnifiedDispatchAddress
import R1UnifiedInitialCase
import R1UnifiedSemanticCase
import R1UnifiedReseedCase
import R1UnifiedOpeningCase
import R1UnifiedQueryCase
import R1UnifiedRhoCase

/-! All 33 actual experiment cases for the single address-dispatched decoder.
The unused row-zero payload codec premise is explicit in this intermediate
composition; a separate canonicalization transfer removes that prover premise. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedDispatchCase

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open TranscriptView

variable {M Cv W : Type} {L : Nat}

private theorem lift_case {X M C I A : Type} [DecidableEq I] [Inhabited A]
    (dec : Dec X M C I A A) (a : I) (T : Table I A)
    (tr : List (I × A)) (out : FS.Prefix X M C × M × C)
    (h : ∃ own pend g, dec a T = some (own, pend, g) ∧
      bfollow g tr own pend T = some out) :
    ∃ own pend g, DecoderStateList.lift dec a T = some (own, pend, g) ∧
      bfollow g tr own pend T = some out := by
  obtain ⟨own, pend, g, hd, hf⟩ := h
  refine ⟨BackgroundOwnMap.map (fun x => [x]) own, pend,
    (fun xs as => g (xs.headD default) as),
    DecoderStateList.lift_of_decode dec a T own pend g hd, ?_⟩
  rw [DecoderStateList.lifted_follow]
  exact hf

theorem decodes_and_follows (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : UnifiedSampler.Prefix M Cv L → Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (prover : Program (Addr L) State (UnifiedProtocol.Proof M))
    (hpub : pub.pubBytes.length < 2^32)
    (hl : ∀ n < 33, p.lbl n = UnifiedLabels.label n)
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
  have hl0 : p.lbl 0 = 160 := (hl 0 (by decide)).trans UnifiedLabels.label_zero
  rw [UnifiedDispatchAddress.decode_at_first p hD extract H pub (eval H prover).2
    _ hpub hl n hn a hfirst]
  by_cases hn0 : n = 0
  · subst n
    rw [UnifiedDecoder.component_initial]
    apply lift_case
    exact UnifiedInitialCase.decodes_and_follows p hD extract decision H pub prover
      hpub Qtot hQ hold a hfirst
  by_cases hn26 : n < 26
  · rw [UnifiedDecoder.component_semantic p hD pub n (by omega) hn26]
    apply lift_case
    exact UnifiedSemanticCase.decodes_and_follows p hD extract decision H pub prover
      hpub hl0 he Qtot hQ hold n (by omega) hn26 a hfirst
  by_cases heq26 : n = 26
  · subst n
    rw [UnifiedDecoder.component_reseed]
    apply lift_case
    exact UnifiedReseedCase.decodes_and_follows p hD extract decision H pub prover
      hpub hl0 he Qtot hQ hold htail a hfirst
  by_cases hn31 : n < 31
  · rw [UnifiedDecoder.component_opening p hD pub n (by omega) hn31]
    apply lift_case
    have hshape : n = 27 + (n - 27) := by omega
    have hcase := UnifiedOpeningCase.decodes_and_follows p hD extract decision H pub prover
      hpub hl0 he Qtot hQ hold htail (n - 27) (by omega) a
      (by simpa only [← hshape] using hfirst)
    simpa only [← hshape] using hcase
  by_cases heq31 : n = 31
  · subst n
    rw [UnifiedDecoder.component_query]
    exact UnifiedQueryCase.decodes_and_follows p hD extract decision H pub prover
      hpub hl0 he Qtot hQ hold htail a hfirst
  have heq32 : n = 32 := by omega
  subst n
  rw [UnifiedDecoder.component_rho]
  apply lift_case
  exact UnifiedRhoCase.decodes_and_follows p hD extract decision H pub prover
    hpub hl0 he Qtot hQ hold htail a hfirst

#print axioms decodes_and_follows

end AspisR1.UnifiedDispatchCase
end
