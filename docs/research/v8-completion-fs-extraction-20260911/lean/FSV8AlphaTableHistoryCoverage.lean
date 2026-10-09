import FSV8AlignedAlphaPairDispositions
import FSV8ProjectedRootLookupAdversaryRecord
import FSV8ProgrammedAlphaCutWitness
import AspisFormal.K1.V7Tag73OracleTableProvenance
import AspisFormal.K1.V7Tag73ProjectedMachinePrefix

/-!
# Query-history coverage along the actual alpha squeeze run

The V8 aligned-state interface deliberately permits an arbitrary initial
cache, so `StateAligned` alone cannot turn a cached alpha call into an earlier
query.  This leaf supplies the missing source invariant.  It first derives
actor-agnostic table/history coverage from a projected adversary run starting
at the literal empty oracle, then proves that ordinary query-only machine runs
and every reached aligned squeeze pair preserve it.

No freshness or probability premise is added.  Programming is kept explicit:
the preservation theorem requires the entry state's programming history to be
empty and proves that it remains empty.  The actual forward-root source uses
only `queryOracle`; a restoration/programmed source must use its separate
programming provenance branch instead of this theorem.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 350000
set_option maxRecDepth 1800

namespace AspisV8Completion.FSV8AlphaTableHistoryCoverage

open FSBoundedTranscript
open FSV8AlignedAlphaSqueezeStep
open FSV8AlignedAlphaChallengeRun
open FSV8AlignedAlphaInitialPairDisposition
open FSV8PostOODGammaScript
open FSV8ExecutablePreAlphaFactorization
open FSV8V7OracleMachineBridge
open FSV8CandidateOriginTrace
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OracleTableProvenance
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73ProjectedMachinePrefix
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K

/-- Every table entry has a matching chronological query record.  Actor and
origin are intentionally not erased from the record itself. -/
def TableCoveredByHistory (state : OracleState) : Prop :=
  ∀ entry ∈ state.table,
    ∃ record ∈ state.history,
      record.input = entry.input ∧ record.output = entry.output

theorem covered_by_query_or_programming_of_history
    (state : OracleState) (covered : TableCoveredByHistory state) :
    TableCoveredByQueryOrProgramming state := by
  intro entry member
  exact Or.inl (covered entry member)

theorem covered_by_history_of_query_or_programming_no_programming
    (state : OracleState) (covered : TableCoveredByQueryOrProgramming state)
    (noProgramming : state.programmingHistory = []) :
    TableCoveredByHistory state := by
  intro entry member
  rcases covered entry member with query | programmed
  · exact query
  · rcases programmed with ⟨record, recordMember, _⟩
    simpa [noProgramming] using recordMember

/-- Any query-only machine segment preserves exact query-history coverage and
the absence of programming records. -/
theorem run_machine_preserves_table_covered_by_history
    {Result : Type*} (controller : AdaptiveController)
    (limits : OracleLimits) (actor : QueryActor) (fuel : Nat)
    (state : OracleState) (program : OracleMachine Result)
    (covered : TableCoveredByHistory state)
    (noProgramming : state.programmingHistory = []) :
    TableCoveredByHistory
        (runMachine controller limits actor fuel state program).oracle ∧
      (runMachine controller limits actor fuel state program).oracle.programmingHistory =
        [] := by
  have covered' := run_machine_preserves_table_covered_by_query_or_programming
    controller limits actor fuel state program
      (covered_by_query_or_programming_of_history state covered)
  have programmingExact := run_machine_preserves_programming_history
    controller limits actor fuel state program
  have noProgramming' :
      (runMachine controller limits actor fuel state program).oracle.programmingHistory =
        [] := programmingExact.trans noProgramming
  exact ⟨covered_by_history_of_query_or_programming_no_programming _ covered'
    noProgramming', noProgramming'⟩

/-- A literal projected adversary run from `emptyOracle` constructs complete
table/history coverage at the actual post-adversary state. -/
theorem projected_adversary_root_table_covered_by_history
    {Result : Type*} (limits : OracleLimits) (fuel : Nat)
    (program : OracleMachine Result) (available : List Digest256)
    (returned : ProjectedMachinePrefixReturned limits .adversary fuel
      emptyOracle program available) :
    TableCoveredByHistory returned.finalState ∧
      returned.finalState.programmingHistory = [] := by
  let controller := controllerFromProjectedFreshAnswers emptyOracle.history
    (returned.freshQueries.map Prod.snd)
  have exactRun := projected_machine_prefix_returned_run_exact limits
    .adversary fuel emptyOracle program available returned
      empty_oracle_history_total_coherent
  have preserved := run_machine_preserves_table_covered_by_history controller
    limits .adversary fuel emptyOracle program (by
      simp [TableCoveredByHistory, emptyOracle]) (by simp [emptyOracle])
  simpa [controller, exactRun] using preserved

/-- The exact selected source/gamma program followed by the exact pre-alpha
program preserves root-derived table/history coverage at the state from which
the live alpha squeeze starts.  The states are definitions of the same
machine runs used by `ProgrammedAlphaCutWitness`; neither is caller-supplied.

This theorem is valid for every halt disposition.  A successful accepted cut
separately identifies the returned boundary and live challenge, while this
leaf supplies the missing table provenance at that boundary. -/
theorem projected_root_constructs_preAlpha_entry_table_coverage
    {Result : Type*} {steps : Nat} {tape : Tape}
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
    TableCoveredByHistory sourceRun.oracle ∧
      sourceRun.oracle.programmingHistory = [] ∧
      TableCoveredByHistory preRun.oracle ∧
      preRun.oracle.programmingHistory = [] := by
  dsimp only
  have rootCovered := projected_adversary_root_table_covered_by_history
    rootLimits rootFuel rootProgram available root
  have sourceCovered := run_machine_preserves_table_covered_by_history
    (controllerFromFreshAnswerTape finiteTape) verifierLimits .verifier
      verifierFuel
      root.finalState
      (compileScript (sourceThenGammaScript firstWork secondWork body digest))
      rootCovered.1 rootCovered.2
  have preCovered := run_machine_preserves_table_covered_by_history
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
      sourceCovered.1 sourceCovered.2
  exact ⟨sourceCovered.1, sourceCovered.2, preCovered.1, preCovered.2⟩

/-- One aligned source pair preserves the actual table/history invariant. -/
theorem AlignedSqueezePair.preserves_table_covered_by_history
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {v7 : OracleState} {s : Transcript}
    (pair : AlignedSqueezePair tape finiteTape limits v7 s)
    (covered : TableCoveredByHistory v7)
    (noProgramming : v7.programmingHistory = []) :
    TableCoveredByHistory pair.afterAdvance ∧
      pair.afterAdvance.programmingHistory = [] := by
  have afterOutput := run_machine_preserves_table_covered_by_history
    (controllerFromFreshAnswerTape finiteTape) limits .verifier 1 v7
      (.query (outputInput s) fun _ => .pure ()) covered noProgramming
  have outputRun :
      runMachine (controllerFromFreshAnswerTape finiteTape) limits .verifier 1
          v7 (.query (outputInput s) fun _ => .pure ()) =
        { halt := .returned (), oracle := pair.afterOutput, steps := 1 } := by
    -- The one-query runner and the pair carry the same successful call.
    simp only [runMachine]
    rw [pair.outputRun]
  have afterOutputCovered : TableCoveredByHistory pair.afterOutput := by
    simpa [outputRun] using afterOutput.1
  have afterOutputNoProgramming : pair.afterOutput.programmingHistory = [] := by
    simpa [outputRun] using afterOutput.2
  have afterAdvance := run_machine_preserves_table_covered_by_history
    (controllerFromFreshAnswerTape finiteTape) limits .verifier 1 pair.afterOutput
      (.query (advanceInput s) fun _ => .pure ()) afterOutputCovered
        afterOutputNoProgramming
  have advanceRun :
      runMachine (controllerFromFreshAnswerTape finiteTape) limits .verifier 1
          pair.afterOutput (.query (advanceInput s) fun _ => .pure ()) =
        { halt := .returned (), oracle := pair.afterAdvance, steps := 1 } := by
    simp only [runMachine]
    rw [pair.advanceRun]
  simpa [advanceRun] using afterAdvance

/-- Coverage is retained at the endpoint of every actually reached rejected
path.  The proof follows the path's concrete pair objects and therefore also
retains their exact history append equations. -/
theorem AlignedRejectedPath.preserves_table_covered_by_history
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {startV7 : OracleState} {start : Transcript}
    {blocks : List Block} {v7 : OracleState} {s : Transcript}
    (path : AlignedRejectedPath tape finiteTape limits startV7 start blocks v7 s)
    (covered : TableCoveredByHistory startV7)
    (noProgramming : startV7.programmingHistory = []) :
    TableCoveredByHistory v7 ∧ v7.programmingHistory = [] := by
  induction path with
  | base aligned prefixPath => exact ⟨covered, noProgramming⟩
  | snoc priorPath pair bounded reject ih =>
      exact
        AspisV8Completion.FSV8AlphaTableHistoryCoverage.AlignedSqueezePair.preserves_table_covered_by_history
          pair ih.1 ih.2

private theorem lookup_entry_some_input_and_member
    (state : OracleState) (input : ShaInput) (entry : TableEntry)
    (found : lookupEntry state input = some entry) :
    entry.input = input ∧ entry ∈ state.table := by
  unfold lookupEntry at found
  have foundSpec := List.find?_eq_some_iff_append.mp found
  exact ⟨of_decide_eq_true foundSpec.1, List.mem_of_find?_eq_some found⟩

private theorem ofFn_has_literal_prefix
    (answer : Digest256) (suffix : List UInt8) :
    HasLiteralStatePrefix answer (List.ofFn answer ++ suffix) := by
  unfold HasLiteralStatePrefix AspisK1.V7Tag73TranscriptSchedule.bytes
  rw [List.take_append_of_le_length (by simp)]
  simp

private theorem next_pair_input_has_advance_answer_prefix
    (tape : Tape) (s : Transcript) (tag : UInt8) :
    HasLiteralStatePrefix (advanceStep tape s).1
      (List.ofFn (squeeze tape s).2.digest ++ [tag]) := by
  change HasLiteralStatePrefix (advanceStep tape s).1
    (List.ofFn (advanceStep tape s).1 ++ [tag])
  exact ofFn_has_literal_prefix _ _

/-- If a later pair encounters a cached input after a fresh preceding advance,
the preceding fresh answer already hit a target available at its own request.

The matching cache record is either older than that request, giving a prior
literal-prefix target, or is the advance record itself, in which case equality
of inputs gives the current-input target.  Thus the proof never counts the
future cached query as though it were known before the fresh answer. -/
theorem fresh_advance_before_cached_next_is_operational_target
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {v7 : OracleState} {s : Transcript}
    (previous : AlignedSqueezePair tape finiteTape limits v7 s)
    (advanceFresh : previous.advanceOrigin = .fresh)
    (covered : TableCoveredByHistory previous.afterAdvance)
    (next : AlignedSqueezePair tape finiteTape limits previous.afterAdvance
      (squeeze tape s).2)
    (nextDisposition : InitialPairDisposition tape finiteTape limits
      previous.afterAdvance (squeeze tape s).2 next)
    (cached :
      (∃ outputOrigin advanceOrigin outputMissing entry advanceFound,
        nextDisposition = .outputFreshAdvanceCached outputOrigin advanceOrigin
          outputMissing entry advanceFound) ∨
      (∃ outputOrigin entry outputFound,
        nextDisposition = .outputCached outputOrigin entry outputFound)) :
    previous.advanceOrigin = .fresh ∧
      (advanceStep tape s).1 ∈ operationalRequestTargets ∅
        previous.afterOutput.history (advanceInput s) := by
  have found : ∃ input entry,
      lookupEntry previous.afterAdvance input = some entry ∧
      (input = outputInput (squeeze tape s).2 ∨
        input = advanceInput (squeeze tape s).2) := by
    rcases cached with advanceCached | outputCached
    · rcases advanceCached with
        ⟨outputOrigin, advanceOrigin, outputMissing, entry, advanceFound,
          dispositionExact⟩
      cases dispositionExact
      exact ⟨advanceInput (squeeze tape s).2, entry, advanceFound,
        Or.inr rfl⟩
    · rcases outputCached with
        ⟨outputOrigin, entry, outputFound, dispositionExact⟩
      cases dispositionExact
      exact ⟨outputInput (squeeze tape s).2, entry, outputFound,
        Or.inl rfl⟩
  rcases found with ⟨input, entry, found, inputKind⟩
  obtain ⟨entryInput, entryMember⟩ :=
    lookup_entry_some_input_and_member previous.afterAdvance input entry found
  obtain ⟨record, recordMember, recordInput, recordOutput⟩ :=
    covered entry entryMember
  have prefixProof : HasLiteralStatePrefix (advanceStep tape s).1 record.input := by
    rw [recordInput, entryInput]
    rcases inputKind with rfl | rfl
    · exact next_pair_input_has_advance_answer_prefix tape s 1
    · exact next_pair_input_has_advance_answer_prefix tape s 2
  have requestHit : OperationalRequestTargetHit ∅ previous.afterOutput.history
      (advanceInput s) (advanceStep tape s).1 := by
    rw [previous.advanceHistory] at recordMember
    rcases List.mem_append.mp recordMember with prior | latest
    · exact .priorLiteralPrefix record prior prefixProof
    · have recordExact : record =
          FSV8AlphaHistoryPhasePrefix.advanceRecord s.digest
            (advanceStep tape s).1 previous.advanceOrigin := by
        simpa using latest
      subst record
      exact .currentLiteralPrefix (by
        simpa [FSV8AlphaHistoryPhasePrefix.advanceRecord, advanceInput,
          AspisK1.V7Tag73TranscriptSchedule.bytes,
          AspisK1.V7Tag73TranscriptSchedule.domAdvance] using prefixProof)
  exact ⟨advanceFresh,
    (operational_request_target_hit_iff_mem ∅ previous.afterOutput.history
      (advanceInput s) (advanceStep tape s).1).mp requestHit⟩

#print axioms covered_by_query_or_programming_of_history
#print axioms covered_by_history_of_query_or_programming_no_programming
#print axioms run_machine_preserves_table_covered_by_history
#print axioms projected_adversary_root_table_covered_by_history
#print axioms projected_root_constructs_preAlpha_entry_table_coverage
#print axioms AlignedSqueezePair.preserves_table_covered_by_history
#print axioms AlignedRejectedPath.preserves_table_covered_by_history
#print axioms fresh_advance_before_cached_next_is_operational_target

end
end AspisV8Completion.FSV8AlphaTableHistoryCoverage
