import R1UnifiedPrefixedReads
import R1UnifiedOpeningRecords
import R1OpeningEndpointCells
import R1OpeningPrefixCompletion

/-! Recover and expose the typed semantic/opening prefix before any of the
four opening rows or the following query row. All cells and reads are derived
from the actual prefixed verifier trace, with explicit collision exclusions. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedOpeningRecovery

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
open TranscriptView

variable {M Cv W : Type} {L : Nat}

theorem recover_before_row (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : UnifiedSampler.Prefix M Cv L → Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M)
    (prior : List (Addr L × State)) (hprior : ∀ q ∈ prior, q.2 = H q.1)
    (hpub : pub.pubBytes.length < 2^32)
    (hl : p.lbl 0 = 160) (he : p.enc (payload 0) = PublicInitFrame.emptyRecord)
    (Qtot : Nat)
    (hQ : firstReads emptyTable
      (UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior) ≤ Qtot)
    (hold : ¬ hitsBad (badColl p Qtot) emptyTable
      (UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior))
    (htail : ¬ hitsBad (ParsedStateCollision.bad TrailingStateFrame.tailState Qtot)
      emptyTable (UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior)) (k : Nat) (hk : k ≤ 4) :
    let tr := UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior
    let c := UnifiedSteps.address p hD H pub c1 payload (27 + k)
    let T := tableBefore emptyTable tr c
    let rs := UnifiedRecords.records p hD H pub c1 payload (27 + k)
    OpeningPrefixCompletion.typed p pub.pubBytes pub.tag T 27 4
      (UnifiedPhases.openingState p hD H pub c1 payload k) = some (c1, rs) ∧
      (∀ r ∈ rs, ∃ b, T b = some r.2.1) ∧
      (∀ r ∈ rs, Read tr (squeezeA p r.2.1)) := by
  dsimp only
  let tr := UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior
  let c := UnifiedSteps.address p hD H pub c1 payload (27 + k)
  let T := tableBefore emptyTable tr c
  let ss := UnifiedPhases.semanticState p hD H pub c1 payload
  let sb := UnifiedRecords.absorbed p hD H pub c1 payload
  let os := UnifiedPhases.openingState p hD H pub c1 payload
  let ob := fun j => UnifiedRecords.absorbed p hD H pub c1 payload (27 + j)
  let om := fun j => payload (27 + j)
  have hcons : ∀ q ∈ tr, q.2 = H q.1 :=
    UnifiedPrefixedReads.trace_consistent p hD extract decision H pub c1 payload prior hprior
  have hi : Read tr (PublicInitFrame.addr pub.pubBytes pub.initFits c1) :=
    UnifiedPrefixedReads.initial_read p hD extract decision H pub c1 payload prior
  have hreads (i : Nat) (hi : i < 33) (hi31 : i ≠ 31) :=
    UnifiedPrefixedReads.ordinary_reads p hD extract decision H pub c1 payload prior hl he i hi hi31
  have hsabs (j : Nat) (hj : j < 27) :
      sb j = H (absorbA p (ss j) (p.lbl j) (p.enc (payload j)) (p.encLen _)) := by
    change _ = H (absorbA p (UnifiedPhases.semanticState p hD H pub c1 payload j) _ _ _)
    rw [UnifiedPhases.semantic_before p hD H pub c1 payload j hj]
    rfl
  have hsar (j : Nat) (hj : j < 27) :
      Read tr (absorbA p (ss j) (p.lbl j) (p.enc (payload j)) (p.encLen _)) := by
    change Read tr (absorbA p (UnifiedPhases.semanticState p hD H pub c1 payload j) _ _ _)
    rw [UnifiedPhases.semantic_before p hD H pub c1 payload j hj]
    exact (hreads j (by omega) (by omega)).1
  have h62 : 62 ≤ L := by have := pub.initFits; omega
  have hr : Read tr (OpeningReseedFrame.addr pub.tag h62 (ss 27)) := by
    change Read tr (OpeningReseedFrame.addr pub.tag h62
      (UnifiedPhases.semanticState p hD H pub c1 payload 27))
    rw [UnifiedPhases.semantic_end]
    exact UnifiedPrefixedReads.reseed_read p hD extract decision H pub c1 payload prior
  have horoot : os 0 = H (OpeningReseedFrame.addr pub.tag h62 (ss 27)) := by
    change UnifiedPhases.openingState p hD H pub c1 payload 0 =
      H (OpeningReseedFrame.addr pub.tag h62
        (UnifiedPhases.semanticState p hD H pub c1 payload 27))
    rw [UnifiedPhases.semantic_end]
    exact UnifiedPhases.opening_root p hD H pub c1 payload
  have hoabs (j : Nat) (hj : j < 4) :
      ob j = H (absorbA p (os j) (p.lbl (27 + j)) (p.enc (om j)) (p.encLen _)) := by
    change _ = H (absorbA p (UnifiedPhases.openingState p hD H pub c1 payload j) _ _ _)
    rw [UnifiedPhases.opening_previous]
    rfl
  have hoar (j : Nat) (hj : j < 4) :
      Read tr (absorbA p (os j) (p.lbl (27 + j)) (p.enc (om j)) (p.encLen _)) := by
    change Read tr (absorbA p (UnifiedPhases.openingState p hD H pub c1 payload j) _ _ _)
    rw [UnifiedPhases.opening_previous]
    exact (hreads (27 + j) (by omega) (by omega)).1
  have hc : Read tr c := by
    by_cases hk4 : k = 4
    · subst k
      have hq := (UnifiedPrefixedReads.query_reads p hD extract decision H pub c1 payload prior).1
      have haddr : UnifiedQueryRun.queryAddress p hD H pub c1 payload =
          UnifiedSteps.address p hD H pub c1 payload 31 :=
        UnifiedSteps.payload_address p hD H pub c1 payload 31 (by decide)
      rw [haddr] at hq
      exact hq
    · exact (hreads (27 + k) (by omega) (by omega)).1
  have hp : c.toBytes.take 32 = bytes (os k) := by
    rw [show os k = UnifiedRecords.previous p hD H pub c1 payload (27 + k) from
      UnifiedPhases.opening_previous p hD H pub c1 payload k]
    exact toBytes_absorbA p _ _ _ _
  have hwalk := OpeningPrefixTrace.walk_before_next p pub.pubBytes hpub pub.initFits c1
    pub.tag h62 H tr Qtot hcons hQ hold htail 27 27 (by decide) (by decide)
    ss sb p.lbl (fun j => p.enc (payload j)) (fun j => p.encLen (payload j))
    (UnifiedPhases.semantic_root p hD H pub c1 payload) hi hsabs
    (UnifiedPhases.semantic_step p hD H pub c1 payload hl he) hsar
    (fun j hj => (hreads j (by omega) (by omega)).2.2) hr
    4 k hk os ob (fun j => p.lbl (27 + j)) (fun j => p.enc (om j))
    (fun j => p.encLen (om j)) horoot (fun j hj => hoabs j (by omega))
    (fun j hj => UnifiedPhases.opening_step p hD H pub c1 payload hl he j (by omega))
    (fun j hj => hoar j (by omega))
    (fun j hj => (hreads (27 + j) (by omega) (by omega)).2.2) c hc hp
  have htyped := OpeningPrefixCompletion.typed_of_walk p pub.pubBytes pub.tag T 27 4
    (os k) c1 ss sb payload 26 os ob om k hwalk
  change OpeningPrefixCompletion.typed p pub.pubBytes pub.tag T 27 4 (os k) =
    some (c1, PrefixRecordFacts.ordinary ss sb payload 26 os ob om k) at htyped
  have hcells := OpeningEndpointCells.cells_before_next p pub.pubBytes hpub pub.initFits c1
    pub.tag h62 H tr Qtot hcons hQ hold htail 27 27 (by decide) (by decide)
    ss sb p.lbl (fun j => p.enc (payload j)) (fun j => p.encLen (payload j))
    (UnifiedPhases.semantic_root p hD H pub c1 payload) hi hsabs
    (UnifiedPhases.semantic_step p hD H pub c1 payload hl he) hsar
    (fun j hj => (hreads j (by omega) (by omega)).2.2) hr
    4 k hk os ob (fun j => p.lbl (27 + j)) (fun j => p.enc (om j))
    (fun j => p.encLen (om j)) horoot (fun j hj => hoabs j (by omega))
    (fun j hj => UnifiedPhases.opening_step p hD H pub c1 payload hl he j (by omega))
    (fun j hj => hoar j (by omega))
    (fun j hj => (hreads (27 + j) (by omega) (by omega)).2.2) c hc hp
  have hknown := PrefixRecordFacts.ordinary_known T ss sb payload 26 os ob om k
    (fun j hj => ⟨absorbA p (ss j) (p.lbl j) (p.enc (payload j)) (p.encLen _),
      (hcells.2.1 j hj).1⟩)
    (fun j hj => ⟨absorbA p (os j) (p.lbl (27 + j)) (p.enc (om j)) (p.encLen _),
      (hcells.2.2.2 j hj).1⟩)
  have hprefixreads := PrefixRecordFacts.ordinary_reads p tr ss sb payload 26 os ob om k
    (fun j hj => (hreads j (by omega) (by omega)).2.1)
    (fun j hj => (hreads (27 + j) (by omega) (by omega)).2.1)
  rw [UnifiedOpeningRecords.ordinary_eq_records_any] at htyped hknown hprefixreads
  exact ⟨htyped, hknown, hprefixreads⟩

#print axioms recover_before_row

end AspisR1.UnifiedOpeningRecovery
end
