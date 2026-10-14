import R1UnifiedPrefixedReads
import R1DuplexRecordPrefix
import R1UnifiedPhases

/-! The decoded semantic records have observed absorb cells and squeeze reads
at a later ordinary endpoint. This is a deterministic trace fact. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedSemanticFacts

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open TranscriptView

variable {M Cv W : Type} {L : Nat}

theorem semantic_records_have_cells_and_squeeze_reads
    (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : UnifiedSampler.Prefix M Cv L → Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M)
    (prior : List (Addr L × State)) (hprior : ∀ q ∈ prior, q.2 = H q.1)
    (hl : p.lbl 0 = 160)
    (he : p.enc (payload 0) = PublicInitFrame.emptyRecord)
    (Qtot : Nat)
    (hQ : firstReads emptyTable
      (UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior) ≤ Qtot)
    (hold : ¬ hitsBad (badColl p Qtot) emptyTable
      (UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior))
    (n : Nat) (hn : 0 < n) (hn26 : n ≤ 26) :
    let tr := UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior
    let c := UnifiedSteps.address p hD H pub c1 payload n
    let rs := UnifiedRecords.records p hD H pub c1 payload n
    (∀ r ∈ rs, ∃ b, tableBefore emptyTable tr c b = some r.2.1) ∧
      (∀ r ∈ rs, Read tr (squeezeA p r.2.1)) := by
  let tr := UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior
  let c := UnifiedSteps.address p hD H pub c1 payload n
  let T := tableBefore emptyTable tr c
  let rs := UnifiedRecords.records p hD H pub c1 payload n
  have hcons : ∀ q ∈ tr, q.2 = H q.1 :=
    UnifiedPrefixedReads.trace_consistent p hD extract decision H pub c1 payload prior hprior
  have hL : 75 + pub.pubBytes.length ≤ L := pub.initFits
  have hroot : UnifiedRecords.previous p hD H pub c1 payload 0 =
      H (PublicInitFrame.addr pub.pubBytes hL c1) := rfl
  have hi : Read tr (PublicInitFrame.addr pub.pubBytes hL c1) :=
    UnifiedPrefixedReads.initial_read p hD extract decision H pub c1 payload prior
  have habs : ∀ j < n, UnifiedRecords.absorbed p hD H pub c1 payload j =
      H (absorbA p (UnifiedRecords.previous p hD H pub c1 payload j)
        (p.lbl j) (p.enc (payload j)) (p.encLen (payload j))) := by
    intro j hj
    rfl
  have hstep : ∀ j < n, UnifiedRecords.previous p hD H pub c1 payload (j + 1) =
      H (advanceA p (UnifiedRecords.absorbed p hD H pub c1 payload j)) := by
    intro j hj
    rw [UnifiedPhases.previous_state p hD H pub c1 payload (j + 1) (by omega)]
    exact UnifiedSteps.state_step p hD H pub c1 payload hl he j (by omega) (by omega)
  have hDdata : ∀ j, (p.enc (payload j)).length ≤ p.D := fun j => p.encLen (payload j)
  have har : ∀ j < n, Read tr
      (absorbA p (UnifiedRecords.previous p hD H pub c1 payload j)
        (p.lbl j) (p.enc (payload j)) (p.encLen (payload j))) := by
    intro j hj
    have hr := UnifiedPrefixedReads.ordinary_reads p hD extract decision H pub c1 payload
      prior hl he j (by omega) (by omega)
    change absorbA p (UnifiedRecords.previous p hD H pub c1 payload j)
      (p.lbl j) (p.enc (payload j)) (p.encLen (payload j)) ∈ tr.map Prod.fst
    simpa only [UnifiedSteps.address] using hr.1
  have hdr : ∀ j < n, Read tr
      (advanceA p (UnifiedRecords.absorbed p hD H pub c1 payload j)) := by
    intro j hj
    exact (UnifiedPrefixedReads.ordinary_reads p hD extract decision H pub c1 payload
      prior hl he j (by omega) (by omega)).2.2
  have hc : Read tr c := by
    exact (UnifiedPrefixedReads.ordinary_reads p hD extract decision H pub c1 payload
      prior hl he n (by omega) (by omega)).1
  have hp : c.toBytes.take 32 =
      bytes (UnifiedRecords.previous p hD H pub c1 payload n) := by
    dsimp [c, UnifiedSteps.address]
    exact toBytes_absorbA p _ _ _ _
  have hcells := DuplexRecordPrefix.table_cells p H tr Qtot hcons hQ hold
    (UnifiedRecords.previous p hD H pub c1 payload)
    (UnifiedRecords.absorbed p hD H pub c1 payload) p.lbl
    (fun j => p.enc (payload j)) hDdata
    (PublicInitFrame.addr pub.pubBytes hL c1) hroot hi n habs hstep har hdr c hc hp
  constructor
  · intro r hr
    change r ∈ (List.range n).map
      (fun j => (UnifiedRecords.previous p hD H pub c1 payload j,
        UnifiedRecords.absorbed p hD H pub c1 payload j, payload j,
        UnifiedRun.state p hD H pub c1 payload (j + 1))) at hr
    rcases List.mem_map.mp hr with ⟨j, hj, hrj⟩
    have hjn : j < n := by simpa using (List.mem_range.mp hj)
    rw [← hrj]
    exact ⟨absorbA p (UnifiedRecords.previous p hD H pub c1 payload j)
      (p.lbl j) (p.enc (payload j)) (p.encLen (payload j)),
      (hcells.2 j hjn).1⟩
  · intro r hr
    change r ∈ (List.range n).map
      (fun j => (UnifiedRecords.previous p hD H pub c1 payload j,
        UnifiedRecords.absorbed p hD H pub c1 payload j, payload j,
        UnifiedRun.state p hD H pub c1 payload (j + 1))) at hr
    rcases List.mem_map.mp hr with ⟨j, hj, hrj⟩
    have hjn : j < n := by simpa using (List.mem_range.mp hj)
    rw [← hrj]
    exact (UnifiedPrefixedReads.ordinary_reads p hD extract decision H pub c1 payload
      prior hl he j (by omega) (by omega)).2.1

#print axioms semantic_records_have_cells_and_squeeze_reads

end AspisR1.UnifiedSemanticFacts
end
