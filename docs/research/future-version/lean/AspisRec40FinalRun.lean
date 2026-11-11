import R1UnifiedPrefixedReads
import R1UnifiedSteps

/-! Aspis 40-row address-level run model: the extension of R1's
`UnifiedProtocol`/`UnifiedVerifier`/`UnifiedTraceReads`/`UnifiedPrefixedReads`
to the 40-row schedule.

R1's `UnifiedRun` (transcript, challenge, state), `UnifiedRecords`
(`previous`, `absorbed`), `UnifiedSteps` (`address`, `state_step`) and
`UnifiedChainReads` (per-row reads) are total in the row number and are
reused unchanged. Only the protocol record (`r := 33`), the verifier and the
trace read lemmas (`i < 33`) are copied here with `r := 40` / `i < 40`.
New: the reads of rows 33 to 39 (`final_reads`), their state steps
(`final_state_step`), and the 40-row verifier trace as R1's verifier trace
followed by the chains of rows 33 to 39 (`verifier_split`). -/
set_option autoImplicit false
noncomputable section
namespace AspisRec40.FinalRun
open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1 AspisR1.TranscriptView

variable {M Cv W : Type} {L : Nat}

/-- Copy of `UnifiedProtocol.protocol` with `r := 40`. -/
def protocol (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W) :
    FS2.Protocol (UnifiedSampler.Public L) (Message M) (Challenge Cv) W
      (UnifiedProtocol.Proof M) (Addr L) State where
  r := 40
  msg := fun π => UnifiedRun.message π.1 π.2
  samp := UnifiedSampler.samp p hD
  decode := fun _ _ => none
  extract := extract

theorem protocol_r1_fields (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W) :
    (protocol p hD extract).samp = (UnifiedProtocol.protocol p hD extract).samp ∧
    (protocol p hD extract).msg = (UnifiedProtocol.protocol p hD extract).msg := ⟨rfl, rfl⟩

/-- Copy of `UnifiedProtocol.transcript_eq`. -/
theorem transcript_eq (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (H : Addr L → State) (pub : UnifiedSampler.Public L) (π : UnifiedProtocol.Proof M) :
    ∀ n, (protocol p hD extract).transcript H pub π n =
      UnifiedRun.transcript p hD H pub π.1 π.2 n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      change
        ((protocol p hD extract).transcript H pub π n).ext
          (UnifiedRun.message π.1 π.2 n)
          (eval H (UnifiedSampler.samp p hD n
            ((protocol p hD extract).transcript H pub π n)
            (UnifiedRun.message π.1 π.2 n)).toProgram).2 =
        (UnifiedRun.transcript p hD H pub π.1 π.2 n).ext
          (UnifiedRun.message π.1 π.2 n)
          (eval H (UnifiedSampler.samp p hD n
            (UnifiedRun.transcript p hD H pub π.1 π.2 n)
            (UnifiedRun.message π.1 π.2 n)).toProgram).2
      rw [ih]

/-- Copy of `UnifiedProtocol.chain_eq`. -/
theorem chain_eq (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (H : Addr L → State) (pub : UnifiedSampler.Public L) (π : UnifiedProtocol.Proof M)
    (i : Nat) :
    (protocol p hD extract).chain H pub π i =
      UnifiedChainReads.chain p hD H pub π.1 π.2 i := by
  change UnifiedSampler.samp p hD i
    ((protocol p hD extract).transcript H pub π i)
    (UnifiedRun.message π.1 π.2 i) = _
  rw [transcript_eq p hD extract H pub π i]
  rfl

/-- Copy of `UnifiedVerifier.verifier` for 40 rows. -/
def verifier (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) → Message M → Bool)
    (pub : UnifiedSampler.Public L) (π : UnifiedProtocol.Proof M) :
    Program (Addr L) State Bool :=
  FS2.verifier (protocol p hD extract) decision pub π

/-- Copy of `UnifiedVerifier.reads`, `i < 40`. -/
theorem reads (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) → Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (π : UnifiedProtocol.Proof M) (i : Nat) (hi : i < 40) (a : Addr L)
    (ha : a ∈ (eval H (UnifiedChainReads.chain p hD H pub π.1 π.2 i).toProgram).1.map Prod.fst) :
    a ∈ (eval H (verifier p hD extract decision pub π)).1.map Prod.fst := by
  apply FS2.verifier_reads (protocol p hD extract) decision H pub π i hi a
  rw [chain_eq p hD extract H pub π i]
  exact ha

/-- The 40-row verifier's trace is R1's 33-row verifier's trace followed by
the chains of rows 33 to 39. -/
theorem verifier_split (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) → Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L) (π : UnifiedProtocol.Proof M) :
    (eval H (verifier p hD extract decision pub π)).1 =
      (eval H (UnifiedVerifier.verifier p hD extract decision pub π)).1 ++
        ((List.range 7).map fun j =>
          (eval H (UnifiedChainReads.chain p hD H pub π.1 π.2 (33 + j)).toProgram).1).flatten := by
  unfold verifier UnifiedVerifier.verifier
  rw [FS2.verifier_eval, FS2.verifier_eval]
  have h40 : (fun j => (eval H ((protocol p hD extract).chain H pub π j).toProgram).1) =
      fun j => (eval H (UnifiedChainReads.chain p hD H pub π.1 π.2 j).toProgram).1 := by
    funext j; rw [chain_eq]
  have h33 : (fun j => (eval H ((UnifiedProtocol.protocol p hD extract).chain H pub π j).toProgram).1) =
      fun j => (eval H (UnifiedChainReads.chain p hD H pub π.1 π.2 j).toProgram).1 := by
    funext j; rw [UnifiedProtocol.chain_eq]; rfl
  dsimp only
  rw [show (protocol p hD extract).r = 33 + 7 from rfl, List.range_add, List.map_append,
    List.flatten_append, h40, h33, List.map_map]
  rfl

/-- The address-level trace of the 40-row run after a prior trace (copy of
`UnifiedPrefixedReads.trace`). -/
def trace (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) → Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) (prior : List (Addr L × State)) : List (Addr L × State) :=
  prior ++ (eval H (verifier p hD extract decision pub (c1, payload))).1

/-- R1's prefixed trace is a prefix of the 40-row trace. -/
theorem trace_r1_prefix (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) → Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) (prior : List (Addr L × State)) :
    ∃ tail, trace p hD extract decision H pub c1 payload prior =
      UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior ++ tail := by
  refine ⟨((List.range 7).map fun j =>
    (eval H (UnifiedChainReads.chain p hD H pub c1 payload (33 + j)).toProgram).1).flatten, ?_⟩
  unfold trace UnifiedPrefixedReads.trace UnifiedTraceReads.trace
  rw [verifier_split, List.append_assoc]

theorem mem_trace (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) → Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) (prior : List (Addr L × State)) (i : Nat) (hi : i < 40)
    (a : Addr L)
    (ha : a ∈ (eval H (UnifiedChainReads.chain p hD H pub c1 payload i).toProgram).1.map Prod.fst) :
    a ∈ (trace p hD extract decision H pub c1 payload prior).map Prod.fst := by
  simp only [trace, List.map_append, List.mem_append]
  exact Or.inr (reads p hD extract decision H pub (c1, payload) i hi a ha)

theorem trace_consistent (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) → Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) (prior : List (Addr L × State))
    (hprior : ∀ q ∈ prior, q.2 = H q.1) :
    ∀ q ∈ trace p hD extract decision H pub c1 payload prior, q.2 = H q.1 := by
  intro q hq
  simp only [trace, List.mem_append] at hq
  rcases hq with hq | hq
  · exact hprior q hq
  · exact FS.eval_consistent H _ q hq

/-- The reads of a plain row `i < 40`, `i ≠ 31` (copy of
`UnifiedPrefixedReads.ordinary_reads`, `i < 33` → `i < 40`). -/
theorem ordinary_reads (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) → Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) (prior : List (Addr L × State))
    (hl : p.lbl 0 = 160) (he : p.enc (payload 0) = PublicInitFrame.emptyRecord)
    (i : Nat) (hi : i < 40) (hi31 : i ≠ 31) :
    UnifiedSteps.address p hD H pub c1 payload i ∈
      (trace p hD extract decision H pub c1 payload prior).map Prod.fst ∧
    squeezeA p (UnifiedRecords.absorbed p hD H pub c1 payload i) ∈
      (trace p hD extract decision H pub c1 payload prior).map Prod.fst ∧
    advanceA p (UnifiedRecords.absorbed p hD H pub c1 payload i) ∈
      (trace p hD extract decision H pub c1 payload prior).map Prod.fst := by
  obtain ⟨ha, hs, hadv⟩ :=
    UnifiedChainReads.ordinary_reads p hD H pub c1 payload hl he i hi31
  exact ⟨mem_trace p hD extract decision H pub c1 payload prior i hi _ ha,
    mem_trace p hD extract decision H pub c1 payload prior i hi _ hs,
    mem_trace p hD extract decision H pub c1 payload prior i hi _ hadv⟩

theorem initial_read (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) → Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) (prior : List (Addr L × State)) :
    PublicInitFrame.addr pub.pubBytes pub.initFits c1 ∈
      (trace p hD extract decision H pub c1 payload prior).map Prod.fst :=
  mem_trace p hD extract decision H pub c1 payload prior 0 (by decide) _
    (UnifiedChainReads.initial_read p hD H pub c1 payload)

theorem reseed_read (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) → Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) (prior : List (Addr L × State)) :
    UnifiedSteps.reseedAddress p hD H pub c1 payload ∈
      (trace p hD extract decision H pub c1 payload prior).map Prod.fst :=
  mem_trace p hD extract decision H pub c1 payload prior 26 (by decide) _
    (UnifiedChainReads.reseed_read p hD H pub c1 payload)

theorem query_reads (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) → Message M → Bool)
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
  obtain ⟨ha, hpairs⟩ := UnifiedQueryReads.row31_reads p hD H pub c1 payload
  refine ⟨mem_trace p hD extract decision H pub c1 payload prior 31 (by decide) _ ha, ?_⟩
  intro j hj
  obtain ⟨hs, hadv⟩ := hpairs j hj
  exact ⟨mem_trace p hD extract decision H pub c1 payload prior 31 (by decide) _ hs,
    mem_trace p hD extract decision H pub c1 payload prior 31 (by decide) _ hadv⟩

/-- The reads of rows 33 to 39. -/
theorem final_reads (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) → Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) (prior : List (Addr L × State))
    (hl : p.lbl 0 = 160) (he : p.enc (payload 0) = PublicInitFrame.emptyRecord)
    (i : Nat) (hlo : 32 ≤ i) (hhi : i < 40) :
    UnifiedSteps.address p hD H pub c1 payload i ∈
      (trace p hD extract decision H pub c1 payload prior).map Prod.fst ∧
    squeezeA p (UnifiedRecords.absorbed p hD H pub c1 payload i) ∈
      (trace p hD extract decision H pub c1 payload prior).map Prod.fst ∧
    advanceA p (UnifiedRecords.absorbed p hD H pub c1 payload i) ∈
      (trace p hD extract decision H pub c1 payload prior).map Prod.fst :=
  ordinary_reads p hD extract decision H pub c1 payload prior hl he i hhi (by omega)

/-- The state after a row `i ≥ 32` is the advance of its absorbed state
(`UnifiedSteps.state_step`, `i ≠ 26, 31`). -/
theorem final_state_step (p : Params M Cv L) (hD : 5 ≤ p.D)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M)
    (hl : p.lbl 0 = 160) (he : p.enc (payload 0) = PublicInitFrame.emptyRecord)
    (i : Nat) (hlo : 32 ≤ i) :
    UnifiedRecords.previous p hD H pub c1 payload (i + 1) =
      H (advanceA p (UnifiedRecords.absorbed p hD H pub c1 payload i)) :=
  UnifiedSteps.state_step p hD H pub c1 payload hl he i (by omega) (by omega)

/-- The absorb frame of row `i ≥ 1` is the address of the 40-row chain's first cell. -/
theorem final_address (p : Params M Cv L) (hD : 5 ≤ p.D)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) (i : Nat) (hi : i ≠ 0) :
    UnifiedSampler.absorb p i (UnifiedRun.transcript p hD H pub c1 payload i) (payload i) =
      absorbA p (UnifiedRecords.previous p hD H pub c1 payload i)
        (p.lbl i) (p.enc (payload i)) (p.encLen (payload i)) :=
  UnifiedSteps.payload_address p hD H pub c1 payload i hi

#print axioms protocol_r1_fields
#print axioms transcript_eq
#print axioms chain_eq
#print axioms reads
#print axioms verifier_split
#print axioms trace_r1_prefix
#print axioms mem_trace
#print axioms trace_consistent
#print axioms ordinary_reads
#print axioms initial_read
#print axioms reseed_read
#print axioms query_reads
#print axioms final_reads
#print axioms final_state_step
#print axioms final_address

end AspisRec40.FinalRun
end
