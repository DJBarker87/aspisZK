import R1UnifiedPrefixedReads

/-! Deterministic first-row reads and challenge for the prefixed unified
verifier trace. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedInitialReads

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open TranscriptView

variable {M Cv W : Type} {L : Nat}

theorem initial_reads (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) →
      Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) (prior : List (Addr L × State)) :
    let init := PublicInitFrame.addr pub.pubBytes pub.initFits c1
    let a := PublicInitFrame.row0 p hD (H init)
    Read (UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior) init ∧
    Read (UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior) a ∧
    Read (UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior)
      (squeezeA p (H a)) ∧
    Read (UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior)
      (advanceA p (H a)) := by
  dsimp only
  let init := PublicInitFrame.addr pub.pubBytes pub.initFits c1
  let a := PublicInitFrame.row0 p hD (H init)
  have hinit : init ∈
      (eval H (UnifiedChainReads.chain p hD H pub c1 payload 0).toProgram).1.map Prod.fst := by
    change init ∈ (eval H (DuplexSamplers.initial p init
      (PublicInitFrame.row0 p hD) 0 liftChallenge).toProgram).1.map Prod.fst
    rw [DuplexSamplers.initial_eval]
    simp [init]
  have ha : a ∈
      (eval H (UnifiedChainReads.chain p hD H pub c1 payload 0).toProgram).1.map Prod.fst := by
    change a ∈ (eval H (DuplexSamplers.initial p init
      (PublicInitFrame.row0 p hD) 0 liftChallenge).toProgram).1.map Prod.fst
    rw [DuplexSamplers.initial_eval]
    simp [a, init]
  have hsq : squeezeA p (H a) ∈
      (eval H (UnifiedChainReads.chain p hD H pub c1 payload 0).toProgram).1.map Prod.fst := by
    change squeezeA p (H a) ∈ (eval H (DuplexSamplers.initial p init
      (PublicInitFrame.row0 p hD) 0 liftChallenge).toProgram).1.map Prod.fst
    rw [DuplexSamplers.initial_eval]
    simp [a, init]
  have hadv : advanceA p (H a) ∈
      (eval H (UnifiedChainReads.chain p hD H pub c1 payload 0).toProgram).1.map Prod.fst := by
    change advanceA p (H a) ∈ (eval H (DuplexSamplers.initial p init
      (PublicInitFrame.row0 p hD) 0 liftChallenge).toProgram).1.map Prod.fst
    rw [DuplexSamplers.initial_eval]
    simp [a, init]
  have hinit' := UnifiedPrefixedReads.initial_read p hD extract decision H pub c1 payload prior
  have hhinit : init ∈ (UnifiedTraceReads.trace p hD extract decision H pub c1 payload).map Prod.fst := by
    exact UnifiedVerifier.reads p hD extract decision H pub (c1, payload) 0 (by decide) init hinit
  have hha : a ∈ (UnifiedTraceReads.trace p hD extract decision H pub c1 payload).map Prod.fst := by
    exact UnifiedVerifier.reads p hD extract decision H pub (c1, payload) 0 (by decide) a ha
  have hhsq : squeezeA p (H a) ∈
      (UnifiedTraceReads.trace p hD extract decision H pub c1 payload).map Prod.fst := by
    exact UnifiedVerifier.reads p hD extract decision H pub (c1, payload) 0 (by decide)
      (squeezeA p (H a)) hsq
  have hhad : advanceA p (H a) ∈
      (UnifiedTraceReads.trace p hD extract decision H pub c1 payload).map Prod.fst := by
    exact UnifiedVerifier.reads p hD extract decision H pub (c1, payload) 0 (by decide)
      (advanceA p (H a)) hadv
  constructor
  · exact hinit'
  constructor
  · simp only [UnifiedPrefixedReads.trace, List.map_append, List.mem_append]
    exact Or.inr hha
  constructor
  · simp only [UnifiedPrefixedReads.trace, List.map_append, List.mem_append]
    exact Or.inr hhsq
  · simp only [UnifiedPrefixedReads.trace, List.map_append, List.mem_append]
    exact Or.inr hhad

theorem initial_challenge (p : Params M Cv L) (hD : 5 ≤ p.D)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) :
    UnifiedRun.challenge p hD H pub c1 payload 0 =
      liftChallenge
        (p.σ 0 (H (squeezeA p (H (PublicInitFrame.row0 p hD
          (H (PublicInitFrame.addr pub.pubBytes pub.initFits c1))))))),
          H (advanceA p (H (PublicInitFrame.row0 p hD
            (H (PublicInitFrame.addr pub.pubBytes pub.initFits c1)))))) := by
  simp only [UnifiedRun.challenge, UnifiedRun.transcript, UnifiedRun.message,
    UnifiedSampler.samp, DuplexSamplers.initial_eval]

#print axioms initial_reads
#print axioms initial_challenge

end AspisR1.UnifiedInitialReads
end
