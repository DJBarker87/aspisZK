import R1UnifiedTraceReads

/-! Read membership survives prefixing the unified verifier trace with an
arbitrary prior trace. Consistency of the combined trace is conditional on
consistency of that prior trace. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedPrefixedReads

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open TranscriptView

variable {M Cv W : Type} {L : Nat}

def trace (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) →
      Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) (prior : List (Addr L × State)) :
    List (Addr L × State) :=
  prior ++ UnifiedTraceReads.trace p hD extract decision H pub c1 payload

theorem initial_read (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) →
      Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) (prior : List (Addr L × State)) :
    PublicInitFrame.addr pub.pubBytes pub.initFits c1 ∈
      (trace p hD extract decision H pub c1 payload prior).map Prod.fst := by
  simp only [trace, List.map_append, List.mem_append]
  exact Or.inr (UnifiedTraceReads.initial_read p hD extract decision H pub c1 payload)

theorem ordinary_reads (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) →
      Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) (prior : List (Addr L × State))
    (hl : p.lbl 0 = 160)
    (he : p.enc (payload 0) = PublicInitFrame.emptyRecord)
    (i : Nat) (hi : i < 33) (hi31 : i ≠ 31) :
    UnifiedSteps.address p hD H pub c1 payload i ∈
      (trace p hD extract decision H pub c1 payload prior).map Prod.fst ∧
    squeezeA p (UnifiedRecords.absorbed p hD H pub c1 payload i) ∈
      (trace p hD extract decision H pub c1 payload prior).map Prod.fst ∧
    advanceA p (UnifiedRecords.absorbed p hD H pub c1 payload i) ∈
      (trace p hD extract decision H pub c1 payload prior).map Prod.fst := by
  obtain ⟨ha, hs, hadv⟩ :=
    UnifiedTraceReads.ordinary_reads p hD extract decision H pub c1 payload hl he i hi hi31
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · simp only [trace, List.map_append, List.mem_append]
    exact Or.inr ha
  · simp only [trace, List.map_append, List.mem_append]
    exact Or.inr hs
  · simp only [trace, List.map_append, List.mem_append]
    exact Or.inr hadv

theorem reseed_read (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) →
      Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) (prior : List (Addr L × State)) :
    UnifiedSteps.reseedAddress p hD H pub c1 payload ∈
      (trace p hD extract decision H pub c1 payload prior).map Prod.fst := by
  simp only [trace, List.map_append, List.mem_append]
  exact Or.inr (UnifiedTraceReads.reseed_read p hD extract decision H pub c1 payload)

theorem query_reads (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) →
      Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) (prior : List (Addr L × State)) :
    let a := UnifiedQueryRun.queryAddress p hD H pub c1 payload
    a ∈ (trace p hD extract decision H pub c1 payload prior).map Prod.fst ∧
    ∀ j, j < 8 →
      squeezeA p (QuerySampler.state p H (H a) j) ∈
        (trace p hD extract decision H pub c1 payload prior).map Prod.fst ∧
      advanceA p (QuerySampler.state p H (H a) j) ∈
        (trace p hD extract decision H pub c1 payload prior).map Prod.fst := by
  dsimp only
  obtain ⟨ha, hpairs⟩ :=
    UnifiedTraceReads.query_reads p hD extract decision H pub c1 payload
  refine ⟨?_, ?_⟩
  · simp only [trace, List.map_append, List.mem_append]
    exact Or.inr ha
  · intro j hj
    obtain ⟨hs, hadv⟩ := hpairs j hj
    exact ⟨by
      simp only [trace, List.map_append, List.mem_append]
      exact Or.inr hs,
      by
      simp only [trace, List.map_append, List.mem_append]
      exact Or.inr hadv⟩

theorem trace_consistent (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) →
      Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) (prior : List (Addr L × State))
    (hprior : ∀ q ∈ prior, q.2 = H q.1) :
    ∀ q ∈ trace p hD extract decision H pub c1 payload prior, q.2 = H q.1 := by
  intro q hq
  simp only [trace, List.mem_append] at hq
  rcases hq with hq | hq
  · exact hprior q hq
  · exact UnifiedTraceReads.trace_consistent p hD extract decision H pub c1 payload q hq

#print axioms initial_read
#print axioms ordinary_reads
#print axioms reseed_read
#print axioms query_reads
#print axioms trace_consistent

end AspisR1.UnifiedPrefixedReads
end
