import FSV8AlphaTableHistoryCoverage

/-!
# Fresh-creator coverage for cached alpha inputs

`TableCoveredByHistory` is enough to prove the local literal-target fact, but
the global native-request bridge retains prior *fresh* verifier records.  This
leaf strengthens the invariant to remember the fresh creator of every table
entry.  It is constructed from the empty projected adversary root and
preserved by the actual query-only source and alpha runs.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 350000
set_option maxRecDepth 1800

namespace AspisV8Completion.FSV8AlphaFreshCreatorCoverage

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73ProjectedMachinePrefix
open AspisK1.V7Tag73TranscriptSchedule
open FSV8CandidateOriginTrace
open FSV8AlignedAlphaSqueezeStep
open FSV8AlignedAlphaChallengeRun
open FSV8PostOODGammaScript
open FSV8ExecutablePreAlphaFactorization
open FSV8V7OracleMachineBridge
open AspisV8Completion.FSV8AlphaTableHistoryCoverage

noncomputable section

abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K

def TableCoveredByFreshHistory (state : OracleState) : Prop :=
  ∀ entry ∈ state.table,
    ∃ record ∈ state.history,
      record.origin = .fresh ∧ record.input = entry.input ∧
        record.output = entry.output

theorem query_oracle_preserves_table_covered_by_fresh_history
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (state nextState : OracleState)
    (input : ShaInput) (output : ShaOutput)
    (covered : TableCoveredByFreshHistory state)
    (success : queryOracle controller limits actor state input =
      .ok (output, nextState)) :
    TableCoveredByFreshHistory nextState := by
  unfold queryOracle at success
  split at success <;> try contradiction
  next _ =>
    split at success
    next entry found =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at success
      rcases success with ⟨rfl, rfl⟩
      intro candidate member
      obtain ⟨record, recordMember, fresh, inputEq, outputEq⟩ :=
        covered candidate member
      exact ⟨record, List.mem_append_left _ recordMember, fresh, inputEq,
        outputEq⟩
    next missing =>
      split at success <;> try contradiction
      next _ =>
        split at success
        next _ => contradiction
        next answer answered =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at success
          rcases success with ⟨rfl, rfl⟩
          intro candidate member
          simp only [List.mem_append, List.mem_singleton] at member
          rcases member with old | rfl
          · obtain ⟨record, recordMember, fresh, inputEq, outputEq⟩ :=
              covered candidate old
            exact ⟨record, List.mem_append_left _ recordMember, fresh,
              inputEq, outputEq⟩
          · let record : QueryRecord :=
              { input := input, output := answer, actor := actor,
                origin := .fresh }
            exact ⟨record, List.mem_append_right _ (by simp [record]), rfl,
              rfl, rfl⟩

theorem run_machine_preserves_table_covered_by_fresh_history
    {Result : Type*} (controller : AdaptiveController)
    (limits : OracleLimits) (actor : QueryActor) (fuel : Nat)
    (state : OracleState) (program : OracleMachine Result)
    (covered : TableCoveredByFreshHistory state) :
    TableCoveredByFreshHistory
      (runMachine controller limits actor fuel state program).oracle := by
  induction fuel generalizing state program with
  | zero => cases program <;> simpa [runMachine] using covered
  | succ fuel ih =>
      cases program with
      | pure result => simpa [runMachine] using covered
      | abort reason => simpa [runMachine] using covered
      | query input next =>
          simp only [runMachine]
          cases queryResult : queryOracle controller limits actor state input with
          | error reason => simpa using covered
          | ok pair =>
              rcases pair with ⟨output, nextState⟩
              exact ih nextState (next output)
                (query_oracle_preserves_table_covered_by_fresh_history
                  controller limits actor state nextState input output covered
                    queryResult)

theorem projected_adversary_root_table_covered_by_fresh_history
    {Result : Type*} (limits : OracleLimits) (fuel : Nat)
    (program : OracleMachine Result) (available : List Digest256)
    (returned : ProjectedMachinePrefixReturned limits .adversary fuel
      emptyOracle program available) :
    TableCoveredByFreshHistory returned.finalState := by
  let controller := controllerFromProjectedFreshAnswers emptyOracle.history
    (returned.freshQueries.map Prod.snd)
  have exactRun := projected_machine_prefix_returned_run_exact limits
    .adversary fuel emptyOracle program available returned
      empty_oracle_history_total_coherent
  have preserved := run_machine_preserves_table_covered_by_fresh_history
    controller limits .adversary fuel emptyOracle program (by
      simp [TableCoveredByFreshHistory, emptyOracle])
  simpa [controller, exactRun] using preserved

theorem projected_root_constructs_preAlpha_entry_fresh_creator_coverage
    {Result : Type*} {steps : Nat}
    (finiteTape : FreshAnswerTape Block steps)
    (rootLimits : OracleLimits) (rootFuel : Nat)
    (verifierLimits : OracleLimits) (verifierFuel : Nat)
    (rootProgram : OracleMachine Result) (available : List Digest256)
    (root : ProjectedMachinePrefixReturned rootLimits .adversary rootFuel
      emptyOracle rootProgram available)
    {n m : Nat}
    (firstWork : Point → FSOracleExecution.Script (List UInt8) Block Unit n)
    (secondWork : Point → Point →
      FSOracleExecution.Script (List UInt8) Block Unit m)
    (body : List UInt8) (digest : Block)
    (out : FSV8PostOODGammaScript.OODResult) (gamma : K)
    (z : Fin 10 → K) (sourceDigest : Block) :
    let sourceRun := runMachine (controllerFromFreshAnswerTape finiteTape)
      verifierLimits .verifier verifierFuel root.finalState
      (compileScript
        (sourceThenGammaScript firstWork secondWork body digest))
    let preRun := runMachine (controllerFromFreshAnswerTape finiteTape)
      verifierLimits .verifier (verifierFuel - sourceRun.steps) sourceRun.oracle
      (compileScript (preAlphaScript out gamma body z sourceDigest))
    TableCoveredByFreshHistory sourceRun.oracle ∧
      TableCoveredByFreshHistory preRun.oracle := by
  dsimp only
  have rootCovered := projected_adversary_root_table_covered_by_fresh_history
    rootLimits rootFuel rootProgram available root
  have sourceCovered := run_machine_preserves_table_covered_by_fresh_history
    (controllerFromFreshAnswerTape finiteTape) verifierLimits .verifier
      verifierFuel root.finalState
      (compileScript (sourceThenGammaScript firstWork secondWork body digest))
      rootCovered
  have preCovered := run_machine_preserves_table_covered_by_fresh_history
    (controllerFromFreshAnswerTape finiteTape) verifierLimits .verifier
      (verifierFuel -
        (runMachine (controllerFromFreshAnswerTape finiteTape) verifierLimits
          .verifier verifierFuel root.finalState
          (compileScript
            (sourceThenGammaScript firstWork secondWork body digest))).steps)
      (runMachine (controllerFromFreshAnswerTape finiteTape) verifierLimits
        .verifier verifierFuel root.finalState
        (compileScript
          (sourceThenGammaScript firstWork secondWork body digest))).oracle
      (compileScript (preAlphaScript out gamma body z sourceDigest))
      sourceCovered
  exact ⟨sourceCovered, preCovered⟩

theorem AlignedSqueezePair.preserves_table_covered_by_fresh_history
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {v7 : OracleState} {s : FSBoundedTranscript.Transcript}
    (pair : AlignedSqueezePair tape finiteTape limits v7 s)
    (covered : TableCoveredByFreshHistory v7) :
    TableCoveredByFreshHistory pair.afterAdvance := by
  have afterOutput := query_oracle_preserves_table_covered_by_fresh_history
    (controllerFromFreshAnswerTape finiteTape) limits .verifier v7
      pair.afterOutput (outputInput s) (outputStep tape s).1 covered
        pair.outputRun
  exact query_oracle_preserves_table_covered_by_fresh_history
    (controllerFromFreshAnswerTape finiteTape) limits .verifier pair.afterOutput
      pair.afterAdvance (advanceInput s) (advanceStep tape s).1 afterOutput
        pair.advanceRun

theorem AlignedRejectedPath.preserves_table_covered_by_fresh_history
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {startV7 : OracleState}
    {start : FSBoundedTranscript.Transcript}
    {blocks : List Block} {v7 : OracleState}
    {s : FSBoundedTranscript.Transcript}
    (path : AlignedRejectedPath tape finiteTape limits startV7 start blocks v7 s)
    (covered : TableCoveredByFreshHistory startV7) :
    TableCoveredByFreshHistory v7 := by
  induction path with
  | base aligned prefixPath => exact covered
  | snoc priorPath pair bounded reject ih =>
      exact
        AspisV8Completion.FSV8AlphaFreshCreatorCoverage.AlignedSqueezePair.preserves_table_covered_by_fresh_history
          pair ih

#print axioms query_oracle_preserves_table_covered_by_fresh_history
#print axioms run_machine_preserves_table_covered_by_fresh_history
#print axioms projected_adversary_root_table_covered_by_fresh_history
#print axioms projected_root_constructs_preAlpha_entry_fresh_creator_coverage
#print axioms AlignedSqueezePair.preserves_table_covered_by_fresh_history
#print axioms AlignedRejectedPath.preserves_table_covered_by_fresh_history

end
end AspisV8Completion.FSV8AlphaFreshCreatorCoverage
