import R1UnifiedPhases
import R1RawRecordSplit
import R1PrefixRecordFacts

/-! The abstract ordinary record list splits at the row-26 reseed into the
semantic prefix and the opening phase, and recombines to the unified run's
first 31 records. This is an index/state-list equality only. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedPhaseRecords

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1.InitialWalk

variable {M Cv : Type} {L : Nat}
variable (p : Params M Cv L) (hD : 5 ≤ p.D) (H : Addr L → State)
  (pub : UnifiedSampler.Public L) (c1 : State) (payload : Nat → M)

theorem ordinary_eq_records :
    PrefixRecordFacts.ordinary
      (UnifiedPhases.semanticState p hD H pub c1 payload)
      (UnifiedRecords.absorbed p hD H pub c1 payload) payload 26
      (UnifiedPhases.openingState p hD H pub c1 payload)
      (fun j => UnifiedRecords.absorbed p hD H pub c1 payload (27 + j))
      (fun j => payload (27 + j)) 4 =
    UnifiedRecords.records p hD H pub c1 payload 31 := by
  have hsemantic :
      RawRoundCompletion.recs
        (UnifiedPhases.semanticState p hD H pub c1 payload)
        (UnifiedRecords.absorbed p hD H pub c1 payload) payload
        (fun j => UnifiedPhases.semanticState p hD H pub c1 payload (j + 1)) 26 =
      RawRoundCompletion.recs
        (UnifiedRecords.previous p hD H pub c1 payload)
        (UnifiedRecords.absorbed p hD H pub c1 payload) payload
        (fun j => UnifiedRun.state p hD H pub c1 payload (j + 1)) 26 := by
    apply RawRecordSplit.recs_congr
    intro j hj
    refine ⟨?_, rfl, rfl, ?_⟩
    · exact UnifiedPhases.semantic_before p hD H pub c1 payload j (by omega)
    · rw [UnifiedPhases.semantic_before p hD H pub c1 payload (j + 1) (by omega),
        UnifiedPhases.previous_state p hD H pub c1 payload (j + 1) (by omega)]
  have hopening :
      RawRoundCompletion.recs
        (UnifiedPhases.openingState p hD H pub c1 payload)
        (fun j => UnifiedRecords.absorbed p hD H pub c1 payload (27 + j))
        (fun j => payload (27 + j))
        (fun j => UnifiedPhases.openingState p hD H pub c1 payload (j + 1)) 4 =
      RawRoundCompletion.recs
        (fun j => UnifiedRecords.previous p hD H pub c1 payload (27 + j))
        (fun j => UnifiedRecords.absorbed p hD H pub c1 payload (27 + j))
        (fun j => payload (27 + j))
        (fun j => UnifiedRun.state p hD H pub c1 payload (28 + j)) 4 := by
    apply RawRecordSplit.recs_congr
    intro j hj
    refine ⟨?_, rfl, rfl, ?_⟩
    · exact UnifiedPhases.opening_previous p hD H pub c1 payload j
    · rw [UnifiedPhases.opening_previous p hD H pub c1 payload (j + 1)]
      rw [UnifiedPhases.previous_state p hD H pub c1 payload (27 + (j + 1)) (by omega)]
      change UnifiedRun.state p hD H pub c1 payload (27 + (j + 1)) =
        UnifiedRun.state p hD H pub c1 payload (28 + j)
      congr 1
      omega
  have hboundary :
      (UnifiedPhases.semanticState p hD H pub c1 payload 26,
        UnifiedRecords.absorbed p hD H pub c1 payload 26, payload 26,
        UnifiedPhases.openingState p hD H pub c1 payload 0) =
      (UnifiedRecords.previous p hD H pub c1 payload 26,
        UnifiedRecords.absorbed p hD H pub c1 payload 26, payload 26,
        UnifiedRun.state p hD H pub c1 payload 27) := by
    rw [UnifiedPhases.semantic_before p hD H pub c1 payload 26 (by omega)]
    rfl
  unfold PrefixRecordFacts.ordinary
  rw [hsemantic, hopening, hboundary]
  change
    (RawRoundCompletion.recs (UnifiedRecords.previous p hD H pub c1 payload)
      (UnifiedRecords.absorbed p hD H pub c1 payload) payload
      (fun j => UnifiedRun.state p hD H pub c1 payload (j + 1)) 26 ++
      [(UnifiedRecords.previous p hD H pub c1 payload 26,
        UnifiedRecords.absorbed p hD H pub c1 payload 26, payload 26,
        UnifiedRun.state p hD H pub c1 payload 27)]) ++
      RawRoundCompletion.recs
        (fun j => UnifiedRecords.previous p hD H pub c1 payload (27 + j))
        (fun j => UnifiedRecords.absorbed p hD H pub c1 payload (27 + j))
        (fun j => payload (27 + j))
        (fun j => UnifiedRun.state p hD H pub c1 payload (28 + j)) 4 =
    RawRoundCompletion.recs (UnifiedRecords.previous p hD H pub c1 payload)
      (UnifiedRecords.absorbed p hD H pub c1 payload) payload
      (fun j => UnifiedRun.state p hD H pub c1 payload (j + 1)) 31
  rw [← RawRoundCompletion.recs_succ
    (UnifiedRecords.previous p hD H pub c1 payload)
    (UnifiedRecords.absorbed p hD H pub c1 payload) payload
    (fun j => UnifiedRun.state p hD H pub c1 payload (j + 1)) 26]
  have hnext :
      (fun j => UnifiedRun.state p hD H pub c1 payload (28 + j)) =
      (fun j => UnifiedRun.state p hD H pub c1 payload (27 + j + 1)) := by
    funext j
    change UnifiedRun.state p hD H pub c1 payload (28 + j) =
      UnifiedRun.state p hD H pub c1 payload ((27 + j) + 1)
    congr 1
    omega
  rw [hnext]
  rw [← RawRecordSplit.recs_split
    (UnifiedRecords.previous p hD H pub c1 payload)
    (UnifiedRecords.absorbed p hD H pub c1 payload) payload
    (fun j => UnifiedRun.state p hD H pub c1 payload (j + 1)) 27 4]
  rfl

#print axioms ordinary_eq_records

end AspisR1.UnifiedPhaseRecords
end
