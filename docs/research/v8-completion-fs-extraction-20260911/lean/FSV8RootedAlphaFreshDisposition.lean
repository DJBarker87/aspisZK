import FSV8ProgrammedAlphaFreshDisposition
import FSV8ProjectedRootLookupAdversaryRecord

/-!
# Four-way alpha origin at an actual post-adversary root

For a projected adversary prefix that starts at `emptyOracle`, a root-table
lookup always has a literal adversary Q1 record.  Hence the apparently
separate `priorTarget`/no-adversary branch is impossible.  The remaining
partition has exactly four cases: adversary Q1, fresh source insertion, fresh
pre-alpha insertion, or absence at the candidate cut.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 350000

namespace AspisV8Completion.FSV8RootedAlphaFreshDisposition

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73ProjectedMachinePrefix
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VerifierOracleStability
open FSV8ProgrammedAlphaCandidateDisposition
open FSV8ProgrammedAlphaFreshDisposition
open FSV8ProjectedRootLookupAdversaryRecord

noncomputable section

inductive RootedFreshAlphaDisposition
    (root sourceState candidateState : OracleState)
    (actor : QueryActor) (input : ShaInput) : Prop where
  | priorAdversary
      (record : QueryRecord)
      (member : record ∈ freezeAdversaryQ1 root)
      (inputEq : record.input = input)
  | introducedDuringSource
      (rootAbsent : lookupEntry root input = none)
      (entry : TableEntry)
      (sourceLookup : lookupEntry sourceState input = some entry)
      (record : QueryRecord)
      (member : record ∈ historySince root sourceState)
      (actorEq : record.actor = actor)
      (fresh : record.origin = .fresh)
      (inputEq : record.input = input)
      (outputEq : record.output = entry.output)
      (entryEq : entry = freshTableEntryOfRecord record)
  | introducedDuringPreAlpha
      (rootAbsent : lookupEntry root input = none)
      (sourceAbsent : lookupEntry sourceState input = none)
      (entry : TableEntry)
      (candidateLookup : lookupEntry candidateState input = some entry)
      (record : QueryRecord)
      (member : record ∈ historySince sourceState candidateState)
      (actorEq : record.actor = actor)
      (fresh : record.origin = .fresh)
      (inputEq : record.input = input)
      (outputEq : record.output = entry.output)
      (entryEq : entry = freshTableEntryOfRecord record)
  | freshAtCandidate
      (rootAbsent : lookupEntry root input = none)
      (candidateAbsent : lookupEntry candidateState input = none)

theorem projected_root_disposition_has_four_cases
    {Result : Type*} (limits : OracleLimits) (fuel : Nat)
    (program : OracleMachine Result) (available : List Digest256)
    (root : ProjectedMachinePrefixReturned limits .adversary fuel emptyOracle
      program available)
    (sourceState candidateState : OracleState) (actor : QueryActor)
    (input : ShaInput)
    (disposition : FreshCausalAlphaDisposition root.finalState sourceState
      candidateState actor input) :
    RootedFreshAlphaDisposition root.finalState sourceState candidateState
      actor input := by
  cases disposition with
  | priorAdversary record member inputEq =>
      exact .priorAdversary record member inputEq
  | priorTarget noAdversary entry lookup =>
      obtain ⟨record, member, _fresh, inputEq, _outputEq⟩ :=
        returned_adversary_root_lookup_has_q1_record limits fuel program
          available root input entry lookup
      exact (noAdversary ⟨record, member, inputEq⟩).elim
  | introducedDuringSource _noAdversary rootAbsent entry sourceLookup record
      member actorEq fresh inputEq outputEq entryEq =>
      exact .introducedDuringSource rootAbsent entry sourceLookup record member
        actorEq fresh inputEq outputEq entryEq
  | introducedDuringPreAlpha _noAdversary rootAbsent sourceAbsent entry
      candidateLookup record member actorEq fresh inputEq outputEq entryEq =>
      exact .introducedDuringPreAlpha rootAbsent sourceAbsent entry
        candidateLookup record member actorEq fresh inputEq outputEq entryEq
  | freshAtCandidate _noAdversary rootAbsent candidateAbsent =>
      exact .freshAtCandidate rootAbsent candidateAbsent

#print axioms projected_root_disposition_has_four_cases

end
end AspisV8Completion.FSV8RootedAlphaFreshDisposition
