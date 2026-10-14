import R1UnifiedInitialReads
import R1UnifiedInitialDecoder
import R1UnifiedFramework

/-! The initial decoder case on the actual prover/verifier experiment.
All four reads and consistency are derived from the evaluator. No row-zero
dummy-payload codec premise or parsed-state collision exclusion is needed. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedInitialCase

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
    (hpub : pub.pubBytes.length < 2^32) (Qtot : Nat)
    (hQ : firstReads emptyTable
      (eval H (FS.experiment prover
        (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1 ≤ Qtot)
    (hold : ¬ hitsBad (badColl p Qtot) emptyTable
      (eval H (FS.experiment prover
        (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1)
    (a : Addr L)
    (hfirst : firstCell ((UnifiedProtocol.protocol p hD extract).chain H pub
      (eval H prover).2 0) = some a) :
    let π := (eval H prover).2
    let tr := (eval H (FS.experiment prover
      (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1
    let T := tableBefore emptyTable tr a
    ∃ own pend g,
      UnifiedInitialDecoder.decode p hD pub a T = some (own, pend, g) ∧
      bfollow g (traceFrom tr a) own pend T =
        some ((UnifiedProtocol.protocol p hD extract).transcript H pub π 0,
          (UnifiedProtocol.protocol p hD extract).msg π 0,
          (UnifiedProtocol.protocol p hD extract).chal H pub π 0) := by
  let π := (eval H prover).2
  let prior := (eval H prover).1
  let tr := (eval H (FS.experiment prover
    (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1
  let init := PublicInitFrame.addr pub.pubBytes pub.initFits π.1
  let start := PublicInitFrame.row0 p hD (H init)
  let T := tableBefore emptyTable tr init
  have hinit := UnifiedFramework.initial_firstCell p hD extract H pub π.1 π.2
  have ha : a = init := Option.some.inj (hfirst.symm.trans hinit)
  subst a
  have htrace : tr =
      UnifiedPrefixedReads.trace p hD extract decision H pub π.1 π.2 prior := by
    dsimp [tr, UnifiedPrefixedReads.trace, UnifiedTraceReads.trace, UnifiedVerifier.verifier]
    rw [FS.experiment_eval]
  have hreads := UnifiedInitialReads.initial_reads p hD extract decision H pub π.1 π.2 prior
  rw [← htrace] at hreads
  have hcons : ∀ q ∈ tr, q.2 = H q.1 := FS.eval_consistent H _
  obtain ⟨own, pend, g, hd, hf⟩ := InitialDecoder.decodes_initializer p hD pub.pubBytes
    hpub pub.initFits π.1 H tr Qtot hcons hQ hold
    hreads.1 hreads.2.1 hreads.2.2.1 hreads.2.2.2
  refine ⟨own, pend, (fun x bs => UnifiedInitialDecoder.view pub (g x bs)), ?_, ?_⟩
  · change (InitialDecoder.decode p hD pub.pubBytes init T).map
        (fun (own, pend, g) => (own, pend, fun x bs => UnifiedInitialDecoder.view pub (g x bs))) = _
    rw [hd]
    rfl
  · have hm := UnifiedInitialDecoder.follows_map (M := M) pub g (traceFrom tr init) own pend T
      (π.1, (p.σ 0 (H (squeezeA p (H start))), H (advanceA p (H start)))) hf
    have hchal : (UnifiedProtocol.protocol p hD extract).chal H pub π 0 =
        liftChallenge (p.σ 0 (H (squeezeA p (H start))), H (advanceA p (H start))) := by
      rw [UnifiedProtocol.chal_eq]
      exact UnifiedInitialReads.initial_challenge p hD H pub π.1 π.2
    rw [hchal]
    exact hm

#print axioms decodes_and_follows

end AspisR1.UnifiedInitialCase
end
