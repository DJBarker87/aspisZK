import AspisFormal.K1.V7Tag73SourceAnchoredSchedulerCut
import AspisFormal.K1.V7Tag73ProjectedFreshPriorQueryHistory

/-!
# Post-adversary root lookups have literal adversary records

The exact V8 root's adversary prefix starts at `emptyOracle`.  Consequently
every table lookup in its returned state was created by one of that prefix's
projected fresh queries.  This leaf turns the table fact into the literal Q1
record needed by the replay extractor.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000

namespace AspisV8Completion.FSV8ProjectedRootLookupAdversaryRecord

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73ProjectedMachinePrefix
open AspisK1.V7Tag73ProjectedFreshPriorQueryHistory
open AspisK1.V7Tag73SourceAnchoredSchedulerCut
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

theorem returned_adversary_root_lookup_has_q1_record
    {Result : Type*} (limits : OracleLimits) (fuel : Nat)
    (program : OracleMachine Result) (available : List Digest256)
    (returned : ProjectedMachinePrefixReturned limits .adversary fuel
      emptyOracle program available)
    (input : ShaInput) (entry : TableEntry)
    (found : lookupEntry returned.finalState input = some entry) :
    ∃ record ∈ freezeAdversaryQ1 returned.finalState,
      record.origin = .fresh ∧ record.input = input ∧
        record.output = entry.output := by
  let cut := SourceAnchoredMachineCut.ofProjectedPrefix limits .adversary fuel
    emptyOracle program available returned
  have foundOutput :
      (lookupEntry returned.finalState input).map TableEntry.output =
        some entry.output := by simp [found]
  have located := source_anchored_machine_cut_lookup_or_future_fresh cut input
    entry.output foundOutput
  rcases located with initial | fresh
  · rcases initial with ⟨initialEntry, initialFound, _⟩
    simp [cut, SourceAnchoredMachineCut.ofProjectedPrefix, emptyOracle,
      lookupEntry] at initialFound
  · let record := projectedFreshQueryRecord .adversary (input, entry.output)
    have recordMember : record ∈ returned.finalState.history :=
      projected_fresh_query_record_mem_final_history limits .adversary
        returned.trace
        (input, entry.output) fresh
    have q1Member : record ∈ freezeAdversaryQ1 returned.finalState := by
      unfold freezeAdversaryQ1 actorHistory
      exact List.mem_filter.mpr ⟨recordMember, by rfl⟩
    exact ⟨record, q1Member, by simp [record, projectedFreshQueryRecord],
      by simp [record, projectedFreshQueryRecord],
      by simp [record, projectedFreshQueryRecord]⟩

#print axioms returned_adversary_root_lookup_has_q1_record

end
end AspisV8Completion.FSV8ProjectedRootLookupAdversaryRecord
