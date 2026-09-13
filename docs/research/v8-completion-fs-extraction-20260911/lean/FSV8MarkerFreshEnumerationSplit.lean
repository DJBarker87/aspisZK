import FSV8MarkerFreshVerifierQueryBridge

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8MarkerFreshEnumerationSplit

open FSOracleExecution
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VerifierOracleStability
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73ProjectedFreshPriorQueryHistory
open FSV8MarkerFreshVerifierQueryBridge

/-- Exact chronological strengthening of marker membership: the prior list is
the fresh-query enumeration of the literal history before the marker. -/
theorem markerFresh_exact_fresh_enumeration_split
    (entryState markerState markerNext finalState : OracleState)
    (actor : QueryActor) (markerInput : ShaInput) (markerAnswer : Digest256)
    (entryPrefix : entryState.history <+: markerState.history)
    (historyExact : markerNext.history = markerState.history ++
      [markerFreshRecord actor markerInput markerAnswer])
    (finalPrefix : markerNext.history <+: finalState.history) :
    ∃ later,
      freshQueryEnumeration (historySince entryState finalState) =
        freshQueryEnumeration (historySince entryState markerState) ++
          [(markerInput, markerAnswer)] ++ later := by
  rcases entryPrefix with ⟨between, markerHistory⟩
  rcases finalPrefix with ⟨after, finalHistory⟩
  rw [historyExact] at finalHistory
  refine ⟨freshQueryEnumeration after, ?_⟩
  unfold historySince
  rw [← finalHistory, ← markerHistory]
  simp [List.append_assoc, markerFreshRecord, freshQueryEnumeration]

theorem fresh_record_pair_mem_fresh_query_enumeration
    (records : List QueryRecord) (record : QueryRecord)
    (member : record ∈ records) (fresh : record.origin = .fresh) :
    (record.input, record.output) ∈ freshQueryEnumeration records := by
  induction records with
  | nil => simp at member
  | cons head tail ih =>
      simp only [List.mem_cons] at member
      rcases member with rfl | tailMember
      · simp [freshQueryEnumeration, fresh]
      · rcases head with ⟨input, output, actor, origin⟩
        cases origin <;> simp only [freshQueryEnumeration, List.mem_cons]
        · exact Or.inr (ih tailMember)
        · exact ih tailMember
        · exact ih tailMember

/-- A concrete fresh verifier record already present before the marker is
present at any request state that retains the entry history and the exact
preceding fresh-query enumeration.  This is the record-level fact needed by
the marker target reduction; cached records are intentionally not covered. -/
theorem fresh_verifier_record_before_marker_mem_request
    (entryState markerState requestState : OracleState)
    (record : QueryRecord)
    (entryPrefix : entryState.history <+: markerState.history)
    (requestEntryPrefix : entryState.history <+: requestState.history)
    (priorHistory : ∀ query ∈
        freshQueryEnumeration (historySince entryState markerState),
      projectedFreshQueryRecord .verifier query ∈ requestState.history)
    (recordMember : record ∈ markerState.history)
    (actorExact : record.actor = .verifier)
    (originExact : record.origin = .fresh) :
    record ∈ requestState.history := by
  rcases entryPrefix with ⟨between, markerHistory⟩
  rw [← markerHistory] at recordMember
  rcases List.mem_append.mp recordMember with entryMember | betweenMember
  · exact requestEntryPrefix.subset entryMember
  · have pairMember : (record.input, record.output) ∈
        freshQueryEnumeration (historySince entryState markerState) := by
      unfold historySince
      rw [← markerHistory]
      simp only [List.drop_append_length]
      exact fresh_record_pair_mem_fresh_query_enumeration between record
        betweenMember originExact
    have retained := priorHistory (record.input, record.output) pairMember
    rcases record with ⟨input, output, actor, origin⟩
    simp only at actorExact originExact
    subst actor
    subst origin
    exact retained

#print axioms markerFresh_exact_fresh_enumeration_split
#print axioms fresh_record_pair_mem_fresh_query_enumeration
#print axioms fresh_verifier_record_before_marker_mem_request

end AspisV8Completion.FSV8MarkerFreshEnumerationSplit
