import FSV8V7OracleMachineBridge
import AspisFormal.K1.V7Tag73ExactCompilerGammaTraceOccurrence

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8ProjectedFreshEnumeration

open FSOracleExecution FSBoundedTranscript
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open FSV8V7OracleMachineBridge

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block

private theorem fresh_record_pair_mem
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

/-- A fresh event in the projected suffix comes from a literal fresh V7
record.  If the source execution establishes that every record in that suffix
belongs to the verifier, the recovered record has that actor as well.  The
prefix premise fixes the chronological suffix rather than treating an
arbitrary list as the post-entry history. -/
theorem projected_fresh_event_recovers_verifier_record
    (entry final : OracleState)
    (event : Event Bytes Block)
    (entryPrefix : entry.history <+: final.history)
    (allVerifier : ∀ record ∈ historySince entry final,
      record.actor = .verifier)
    (eventFresh : event.fresh = true)
    (eventMem : event ∈
      (final.history.map projectRecord).drop entry.history.length) :
    ∃ record,
      record ∈ historySince entry final ∧
      record.actor = .verifier ∧
      record.origin = .fresh ∧
      projectRecord record = event := by
  rcases entryPrefix with ⟨suffix, finalHistory⟩
  have suffixExact : historySince entry final = suffix := by
    unfold historySince
    rw [← finalHistory]
    exact List.drop_append_length
  have mappedMem : event ∈ suffix.map projectRecord := by
    rw [← finalHistory, List.map_append] at eventMem
    have lengthExact : entry.history.length =
        (entry.history.map projectRecord).length := by simp
    rw [lengthExact, List.drop_append_length] at eventMem
    exact eventMem
  obtain ⟨record, recordMem, recordEq⟩ := List.mem_map.mp mappedMem
  have recordSuffix : record ∈ historySince entry final := by
    rw [suffixExact]
    exact recordMem
  have actorExact : record.actor = .verifier :=
    allVerifier record recordSuffix
  have projectedFresh : (projectRecord record).fresh = true := by
    rw [recordEq]
    exact eventFresh
  have originExact : record.origin = .fresh := by
    rcases record with ⟨input, output, actor, origin⟩
    cases origin <;>
      simp [projectRecord, projectOrigin] at projectedFresh ⊢
  exact ⟨record, recordSuffix, actorExact, originExact, recordEq⟩

/-- Consumer form used by the alpha candidate bridge: a fresh projected event
in the chronological suffix contributes its exact input/answer pair to the
V7 fresh-query enumeration.  Cached and programmed records cannot satisfy the
`eventFresh` premise. -/
theorem projected_fresh_event_mem_freshQueryEnumeration
    (entry final : OracleState)
    (event : Event Bytes Block)
    (entryPrefix : entry.history <+: final.history)
    (allVerifier : ∀ record ∈ historySince entry final,
      record.actor = .verifier)
    (eventFresh : event.fresh = true)
    (eventMem : event ∈
      (final.history.map projectRecord).drop entry.history.length) :
    (event.input, event.answer) ∈
      freshQueryEnumeration (historySince entry final) := by
  obtain ⟨record, recordMem, _actorExact, originExact, recordEq⟩ :=
    projected_fresh_event_recovers_verifier_record entry final event
      entryPrefix allVerifier eventFresh eventMem
  have pairMem := fresh_record_pair_mem
    (historySince entry final) record recordMem originExact
  have inputEq : record.input = event.input :=
    congrArg (fun value : Event Bytes Block => value.input) recordEq
  have answerEq : record.output = event.answer :=
    congrArg (fun value : Event Bytes Block => value.answer) recordEq
  rw [← inputEq, ← answerEq]
  exact pairMem

#print axioms projected_fresh_event_recovers_verifier_record
#print axioms projected_fresh_event_mem_freshQueryEnumeration

end AspisV8Completion.FSV8ProjectedFreshEnumeration
