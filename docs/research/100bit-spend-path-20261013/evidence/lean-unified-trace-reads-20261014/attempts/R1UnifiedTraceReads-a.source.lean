import R1UnifiedChainReads
import R1UnifiedVerifier
import R1UnifiedQueryReads

/-! Lift the symbolic unified sampler's first reads into the complete FS2
verifier trace for the same proof tuple. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedTraceReads

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open TranscriptView

variable {M Cv W : Type} {L : Nat}

def trace (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) →
      Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) : List (Addr L × State) :=
  (eval H (UnifiedVerifier.verifier p hD extract decision pub (c1, payload))).1

theorem initial_read (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) →
      Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) :
    PublicInitFrame.addr pub.pubBytes pub.initFits c1 ∈
      (trace p hD extract decision H pub c1 payload).map Prod.fst := by
  exact UnifiedVerifier.reads p hD extract decision H pub (c1, payload)
    0 (by decide) _ (UnifiedChainReads.initial_read p hD H pub c1 payload)

theorem ordinary_reads (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) →
      Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M)
    (hl : p.lbl 0 = 160)
    (he : p.enc (payload 0) = PublicInitFrame.emptyRecord)
    (i : Nat) (hi : i < 33) (hi31 : i ≠ 31) :
    UnifiedSteps.address p hD H pub c1 payload i ∈
      (trace p hD extract decision H pub c1 payload).map Prod.fst ∧
    squeezeA p (UnifiedRecords.absorbed p hD H pub c1 payload i) ∈
      (trace p hD extract decision H pub c1 payload).map Prod.fst ∧
    advanceA p (UnifiedRecords.absorbed p hD H pub c1 payload i) ∈
      (trace p hD extract decision H pub c1 payload).map Prod.fst := by
  obtain ⟨ha, hs, hadv⟩ :=
    UnifiedChainReads.ordinary_reads p hD H pub c1 payload hl he i hi31
  exact ⟨UnifiedVerifier.reads p hD extract decision H pub (c1, payload) i hi _ ha,
    UnifiedVerifier.reads p hD extract decision H pub (c1, payload) i hi _ hs,
    UnifiedVerifier.reads p hD extract decision H pub (c1, payload) i hi _ hadv⟩

theorem reseed_read (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) →
      Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) :
    UnifiedSteps.reseedAddress p hD H pub c1 payload ∈
      (trace p hD extract decision H pub c1 payload).map Prod.fst := by
  exact UnifiedVerifier.reads p hD extract decision H pub (c1, payload)
    26 (by decide) _ (UnifiedChainReads.reseed_read p hD H pub c1 payload)

theorem query_reads (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) →
      Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) :
    let a := UnifiedQueryRun.queryAddress p hD H pub c1 payload
    a ∈ (trace p hD extract decision H pub c1 payload).map Prod.fst ∧
    ∀ j, j < 8 →
      squeezeA p (QuerySampler.state p H (H a) j) ∈
        (trace p hD extract decision H pub c1 payload).map Prod.fst ∧
      advanceA p (QuerySampler.state p H (H a) j) ∈
        (trace p hD extract decision H pub c1 payload).map Prod.fst := by
  dsimp
  obtain ⟨ha, hpairs⟩ := UnifiedQueryReads.row31_reads p hD H pub c1 payload
  refine ⟨UnifiedVerifier.reads p hD extract decision H pub (c1, payload)
      31 (by decide) _ ha, ?_⟩
  intro j hj
  obtain ⟨hs, hadv⟩ := hpairs j hj
  exact ⟨UnifiedVerifier.reads p hD extract decision H pub (c1, payload)
      31 (by decide) _ hs,
    UnifiedVerifier.reads p hD extract decision H pub (c1, payload)
      31 (by decide) _ hadv⟩

theorem trace_consistent (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) →
      Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) :
    ∀ q ∈ trace p hD extract decision H pub c1 payload, q.2 = H q.1 := by
  exact UnifiedVerifier.trace_consistent p hD extract decision H pub (c1, payload)

#print axioms initial_read
#print axioms ordinary_reads
#print axioms reseed_read
#print axioms query_reads
#print axioms trace_consistent

end AspisR1.UnifiedTraceReads
end
