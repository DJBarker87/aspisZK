import R1UnifiedPrefixedReads
import R1UnifiedPhaseRecords
import R1OpeningQueryTrace

/-! Instantiate the existing prefix/query recovery theorem with the actual
unified verifier run. Read membership and phase transitions are derived.
The first-read budget and the two collision exclusions remain explicit. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedRecovery

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
open TranscriptView

variable {M Cv W : Type} {L : Nat}

theorem recover_and_follow (p : Params M Cv L) (hD : 5 ≤ p.D)
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
      emptyTable (UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior)) :
    let tr := UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior
    let a := UnifiedQueryRun.queryAddress p hD H pub c1 payload
    let c := UnifiedQueryRun.rhoAddress p hD H pub c1 payload
    let T := tableBefore emptyTable tr c
    let rs := UnifiedRecords.records p hD H pub c1 payload 31
    let qr := UnifiedQueryRun.queryResult p hD H pub c1 payload
    OpeningPrefixCompletion.typed p pub.pubBytes pub.tag T 27 4
      (UnifiedPhases.openingState p hD H pub c1 payload 4) = some (c1, rs) ∧
    bfollow (JointNextLaw.output p T rs qr.2 32)
      (traceFrom tr c) (QueryNextLaw.own p c)
      ((JointPrefixAnswers.missing p T rs qr.2).map fun b => (b, none)) T =
      some ((completeRounds p emptyTable H 0 rs, some (a, qr)),
        (p.σ 32 (H (squeezeA p (H c))), H (advanceA p (H c)))) := by
  dsimp only
  let tr := UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior
  let a := UnifiedQueryRun.queryAddress p hD H pub c1 payload
  let c := UnifiedQueryRun.rhoAddress p hD H pub c1 payload
  let ss := UnifiedPhases.semanticState p hD H pub c1 payload
  let sb := UnifiedRecords.absorbed p hD H pub c1 payload
  let os := UnifiedPhases.openingState p hD H pub c1 payload
  let ob := fun j => UnifiedRecords.absorbed p hD H pub c1 payload (27 + j)
  let om := fun j => payload (27 + j)
  let qs := QuerySampler.state p H (H a)
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
  have hqr := UnifiedPrefixedReads.query_reads p hD extract decision H pub c1 payload prior
  have ha : Read tr a := hqr.1
  have hca0 : c = UnifiedSteps.address p hD H pub c1 payload 32 :=
    UnifiedSteps.payload_address p hD H pub c1 payload 32 (by decide)
  have hc : Read tr c := by rw [hca0]; exact (hreads 32 (by decide) (by decide)).1
  have hcabs : H c = sb 32 := by rw [hca0]; rfl
  have hqa : a = absorbA p (os 4) (p.lbl 31) (p.enc (payload 31)) (p.encLen _) := by
    change UnifiedSampler.absorb p 31 (UnifiedRun.transcript p hD H pub c1 payload 31)
      (payload 31) = absorbA p (UnifiedPhases.openingState p hD H pub c1 payload 4) _ _ _
    rw [UnifiedSteps.payload_address p hD H pub c1 payload 31 (by decide),
      UnifiedPhases.opening_previous]
    rfl
  have hca : c = absorbA p (QueryFirstRead.result p H qs).2 (p.lbl 32)
      (p.enc (payload 32)) (p.encLen _) :=
    UnifiedQueryRun.rho_address p hD H pub c1 payload
  have hparsea : (parseAbsorb a).isSome := by rw [hqa, parseAbsorb_absorbA]; rfl
  have hparsec : (parseAbsorb c).isSome := by rw [hca, parseAbsorb_absorbA]; rfl
  have haprefix : a.toBytes.take 32 = bytes (os 4) := by
    rw [hqa]; exact toBytes_absorbA p _ _ _ _
  have hcprefix : c.toBytes.take 32 = bytes (QueryFirstRead.result p H qs).2 := by
    rw [hca]; exact toBytes_absorbA p _ _ _ _
  have hnewsq : Read tr (squeezeA p (H c)) := by
    rw [hcabs]; exact (hreads 32 (by decide) (by decide)).2.1
  have hnewadv : Read tr (advanceA p (H c)) := by
    rw [hcabs]; exact (hreads 32 (by decide) (by decide)).2.2
  have hf := OpeningQueryTrace.recover_and_follow p pub.pubBytes hpub pub.initFits c1
    pub.tag h62 H tr Qtot hcons hQ hold htail 27 26 (by decide)
    ss sb payload (fun j => p.encLen (payload j))
    (UnifiedPhases.semantic_root p hD H pub c1 payload) hi hsabs
    (UnifiedPhases.semantic_step p hD H pub c1 payload hl he) hsar
    (fun j hj => (hreads j (by omega) (by omega)).2.2)
    (fun j hj => (hreads j (by omega) (by omega)).2.1) hr
    4 4 (by decide) os ob om (fun j => p.encLen (om j)) horoot hoabs
    (UnifiedPhases.opening_step p hD H pub c1 payload hl he) hoar
    (fun j hj => (hreads (27 + j) (by omega) (by omega)).2.2)
    (fun j hj => (hreads (27 + j) (by omega) (by omega)).2.1)
    qs (fun j _ => QuerySamplerBridge.state_step p H (H a) j)
    (fun j hj => (hqr.2 j hj).2) (fun j hj => (hqr.2 j hj).1)
    a c ha hc hparsea hparsec haprefix rfl hcprefix hnewsq hnewadv
  dsimp only at hf
  change _ ∧ _ at hf
  rw [UnifiedPhaseRecords.ordinary_eq_records] at hf
  exact hf

#print axioms recover_and_follow

end AspisR1.UnifiedRecovery
end
