import FSV8ProgrammedAlphaCandidateDisposition
import AspisFormal.K1.V7Tag73OracleTableProvenance
import AspisFormal.K1.V7Tag73VerifierOracleStability

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 350000

namespace AspisV8Completion.FSV8ProgrammedAlphaPrefixInsertionProvenance

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OracleTableProvenance
open AspisK1.V7Tag73VerifierOracleStability
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSV8V7OracleMachineBridge
open FSV8PostOODGammaScript
open FSV8ExecutablePreAlphaFactorization
open FSV8ProgrammedAlphaCandidateDisposition

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K

/-! The two machine segments below are deliberately kept generic.  The only
    source of a causal record is the machine's exported `historySince`; no
    actor-coverage or probability premise is hidden in this statement. -/

theorem segment_lookup_has_causal_record
    {Result : Type*}
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat)
    (root : OracleState) (program : OracleMachine Result)
    (input : ShaInput) (entry : TableEntry)
    (rootMissing : lookupEntry root input = none)
    (found : lookupEntry
      (runMachine controller limits actor fuel root program).oracle input =
        some entry) :
    ∃ record ∈ historySince root
        (runMachine controller limits actor fuel root program).oracle,
      record.actor = actor ∧ record.input = input ∧
        record.output = entry.output := by
  have foundSpec : entry.input = input := by
    unfold lookupEntry at found
    exact of_decide_eq_true (List.find?_eq_some_iff_append.mp found).1
  have entryMember :
      entry ∈ (runMachine controller limits actor fuel root program).oracle.table := by
    unfold lookupEntry at found
    exact List.mem_of_find?_eq_some found
  have covered := run_machine_table_covered_by_entry_or_history_since
    controller limits actor fuel root program entry entryMember
  rcases covered with rootMember | witness
  · unfold lookupEntry at rootMissing
    have rejected := List.find?_eq_none.mp rootMissing entry rootMember
    simp [foundSpec] at rejected
  · rcases witness with ⟨record, recordMember, inputEq, outputEq⟩
    have exactRun := run_machine_exact_fresh_extension
      controller limits actor fuel root program
    exact ⟨record, recordMember, (exactRun.2.1 record recordMember).1,
      inputEq.trans foundSpec, outputEq⟩

theorem two_segment_lookup_has_causal_record
    {Result₁ Result₂ : Type*}
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel₁ fuel₂ : Nat)
    (root : OracleState) (firstProgram : OracleMachine Result₁)
    (secondProgram : OracleMachine Result₂) (input : ShaInput)
    (entry : TableEntry)
    (rootMissing : lookupEntry root input = none)
    (found : lookupEntry
      (runMachine controller limits actor fuel₂
        (runMachine controller limits actor fuel₁ root firstProgram).oracle
        secondProgram).oracle input = some entry) :
    (∃ record ∈ historySince root
        (runMachine controller limits actor fuel₁ root firstProgram).oracle,
        record.actor = actor ∧ record.input = input ∧
          record.output = entry.output) ∨
    (∃ record ∈ historySince
        (runMachine controller limits actor fuel₁ root firstProgram).oracle
        (runMachine controller limits actor fuel₂
          (runMachine controller limits actor fuel₁ root firstProgram).oracle
          secondProgram).oracle,
        record.actor = actor ∧ record.input = input ∧
          record.output = entry.output) := by
  let first := runMachine controller limits actor fuel₁ root firstProgram
  let second := runMachine controller limits actor fuel₂ first.oracle secondProgram
  have foundSpec : entry.input = input := by
    unfold lookupEntry at found
    exact of_decide_eq_true (List.find?_eq_some_iff_append.mp found).1
  have entryMember : entry ∈ second.oracle.table := by
    unfold lookupEntry at found
    exact List.mem_of_find?_eq_some found
  have secondCovered := run_machine_table_covered_by_entry_or_history_since
    controller limits actor fuel₂ first.oracle secondProgram entry entryMember
  rcases secondCovered with initialMember | secondWitness
  · have firstCovered := run_machine_table_covered_by_entry_or_history_since
      controller limits actor fuel₁ root firstProgram entry initialMember
    rcases firstCovered with rootMember | firstWitness
    · unfold lookupEntry at rootMissing
      have rejected := List.find?_eq_none.mp rootMissing entry rootMember
      simp [foundSpec] at rejected
    · rcases firstWitness with ⟨record, recordMember, inputEq, outputEq⟩
      have exactFirst := run_machine_exact_fresh_extension
        controller limits actor fuel₁ root firstProgram
      left
      exact ⟨record, recordMember,
        (exactFirst.2.1 record recordMember).1,
        inputEq.trans foundSpec, outputEq⟩
  · rcases secondWitness with ⟨record, recordMember, inputEq, outputEq⟩
    have exactSecond := run_machine_exact_fresh_extension
      controller limits actor fuel₂ first.oracle secondProgram
    right
    exact ⟨record, recordMember,
      (exactSecond.2.1 record recordMember).1,
      inputEq.trans foundSpec, outputEq⟩

/-! The source-shaped five-way classifier.  Unlike the earlier endpoint-only
    classifier, both insertion branches carry an actual chronological record
    from the precise machine segment in which the table entry appeared.  The
    displayed record need not itself be the first/fresh record for the input. -/

inductive StrongCausalAlphaDisposition
    (root sourceState candidateState : OracleState)
    (actor : QueryActor) (input : ShaInput) : Prop where
  | priorAdversary
      (record : QueryRecord)
      (member : record ∈ freezeAdversaryQ1 root)
      (inputEq : record.input = input)
  | priorTarget
      (noAdversary : NoPriorAdversaryInput root input)
      (entry : TableEntry)
      (lookup : lookupEntry root input = some entry)
  | introducedDuringSource
      (noAdversary : NoPriorAdversaryInput root input)
      (rootAbsent : lookupEntry root input = none)
      (sourceEntry candidateEntry : TableEntry)
      (sourceLookup : lookupEntry sourceState input = some sourceEntry)
      (candidateLookup : lookupEntry candidateState input = some candidateEntry)
      (record : QueryRecord)
      (member : record ∈ historySince root sourceState)
      (actorEq : record.actor = actor)
      (inputEq : record.input = input)
      (outputEq : record.output = sourceEntry.output)
  | introducedDuringPreAlpha
      (noAdversary : NoPriorAdversaryInput root input)
      (rootAbsent : lookupEntry root input = none)
      (entry : TableEntry)
      (sourceAbsent : lookupEntry sourceState input = none)
      (candidateLookup : lookupEntry candidateState input = some entry)
      (record : QueryRecord)
      (member : record ∈ historySince sourceState candidateState)
      (actorEq : record.actor = actor)
      (inputEq : record.input = input)
      (outputEq : record.output = entry.output)
  | freshAtCandidate
      (noAdversary : NoPriorAdversaryInput root input)
      (rootAbsent : lookupEntry root input = none)
      (candidateAbsent : lookupEntry candidateState input = none)

/-- Strengthen the endpoint disposition produced by the exact programmed cut.
    The only nontrivial case is table insertion between the two cuts; the
    generic segment provenance theorem splits it at the real source/pre-alpha
    boundary and supplies a matching query record from the segment in which
    the entry appeared. -/
theorem programmed_candidate_constructs_strong_disposition
    {steps : Nat}
    (finiteTape : FreshAnswerTape Block steps)
    (limits : OracleLimits) (actor : QueryActor)
    {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (body : Bytes) (digest : Block)
    (v7 : OracleState) (fuel : Nat)
    (programmed : ProgrammedAlphaCandidateDisposition finiteTape limits actor
      firstWork secondWork z body digest v7 fuel) :
    ∃ out : FSV7OODBodyScript.Result, ∃ gamma : K,
      ∃ sourceDigest : Block,
      ∃ boundary : FSV8ExecutablePreAlphaFactorization.PreAlpha
        out gamma body z,
        let sourceRun := sourceMachineRun finiteTape limits actor firstWork
          secondWork body digest v7 fuel
        let preRun := preAlphaMachineRun finiteTape limits actor firstWork
          secondWork body digest v7 fuel out gamma z sourceDigest
        StrongCausalAlphaDisposition v7 sourceRun.oracle preRun.oracle actor
          (List.ofFn boundary.digest ++ [1]) := by
  rcases programmed with ⟨out, gamma, sourceDigest, boundary, _prefixDigest,
    _alpha0, _candidateDigest, _candidateOutput, _candidateNextState,
    _candidateOrigin, _sourceReturned, _preReturned, _candidateReturned,
    _firstInput, _candidateQuery, _candidateHistory, disposition⟩
  refine ⟨out, gamma, sourceDigest, boundary, ?_⟩
  let sourceRun := sourceMachineRun finiteTape limits actor firstWork secondWork
    body digest v7 fuel
  let preRun := preAlphaMachineRun finiteTape limits actor firstWork secondWork
    body digest v7 fuel out gamma z sourceDigest
  cases disposition with
  | priorAdversary record member inputEq =>
      exact .priorAdversary record member inputEq
  | priorTarget noAdversary entry lookup =>
      exact .priorTarget noAdversary entry lookup
  | freshAtCandidate noAdversary rootAbsent candidateAbsent =>
      exact .freshAtCandidate noAdversary rootAbsent candidateAbsent
  | introducedDuringVerifier noAdversary rootAbsent entry candidateLookup =>
      cases sourceLookup :
          lookupEntry sourceRun.oracle
            (List.ofFn boundary.digest ++ [1]) with
      | some sourceEntry =>
          have sourceWitness := segment_lookup_has_causal_record
            (controllerFromFreshAnswerTape finiteTape) limits actor fuel v7
            (compileScript
              (sourceThenGammaScript firstWork secondWork body digest))
            (List.ofFn boundary.digest ++ [1]) sourceEntry rootAbsent
            (by simpa [sourceRun, sourceMachineRun] using sourceLookup)
          rcases sourceWitness with
            ⟨record, member, actorEq, inputEq, outputEq⟩
          refine .introducedDuringSource noAdversary rootAbsent sourceEntry
            entry sourceLookup candidateLookup record ?_ actorEq inputEq
            outputEq
          unfold sourceMachineRun
          exact member
      | none =>
          have preWitness := segment_lookup_has_causal_record
            (controllerFromFreshAnswerTape finiteTape) limits actor
            (fuel - sourceRun.steps) sourceRun.oracle
            (compileScript (preAlphaScript out gamma body z sourceDigest))
            (List.ofFn boundary.digest ++ [1]) entry sourceLookup
            (by simpa [preRun, preAlphaMachineRun] using candidateLookup)
          rcases preWitness with
            ⟨record, member, actorEq, inputEq, outputEq⟩
          refine .introducedDuringPreAlpha noAdversary rootAbsent entry
            sourceLookup candidateLookup record ?_ actorEq inputEq outputEq
          unfold sourceMachineRun preAlphaMachineRun
          exact member

#print axioms segment_lookup_has_causal_record
#print axioms two_segment_lookup_has_causal_record
#print axioms programmed_candidate_constructs_strong_disposition

end AspisV8Completion.FSV8ProgrammedAlphaPrefixInsertionProvenance
