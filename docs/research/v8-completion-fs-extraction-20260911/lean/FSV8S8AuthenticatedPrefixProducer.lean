import FSV8S8RootFunctionalCuts
import FSV7PrefixBridge
import SameBodyAuthenticatedSlots
import AspisFormal.K1.V7Tag73K12BudgetedSchedulerTree

/-!
# Source-produced authenticated prefixes for the S8 terminal root

The two advertised answer prefixes and the full old-style Merkle log are
projections of one actual accepted terminal-root execution.  No
`AnswerPrefix`, `OrderedRawQueryLog`, answer-agreement fact, or inclusion fact
is supplied by the caller.

The C2 prefix is the conservative post-C2-absorb execution cut.  It is still
strictly before OOD, gamma and authenticated openings; proving equivalence to
the sharper pre-C2-absorb cut is a separate optimization, not used here.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 350000
set_option maxRecDepth 1800

namespace AspisV8Completion.FSV8S8AuthenticatedPrefixProducer

open FSOracleExecution FSBoundedTranscript FSExposureOrder
open FSAuthenticationPrefixes FSV7PrefixBridge
open FSV8V7OracleMachineBridge FSV8V7WholeScriptUniformLaw
open FSV8S8RootFunctionalCuts
open FSV8S7DynamicSelectedRoot
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73ProjectedMachinePrefix
open AspisK1.V7Tag73K12BudgetedSchedulerTree
open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7MerkleOpeningBinding
open AspisV8.AuthenticatedEarlyC1Prefix

noncomputable section

abbrev Block := FSBoundedTranscript.Block

def finalOracle
    {HiddenTape TapeIdentity Observation : Type}
    {globalOracleCalls steps : Nat}
    {configuration : DynamicConfiguration HiddenTape TapeIdentity Observation
      globalOracleCalls}
    {hidden : HiddenTape} {finiteTape : FreshAnswerTape Block steps}
    {fallback : Block}
    {runtime : FSV8S8SelectedOrdinaryTerminal.Runtime TapeIdentity}
    {accepted : FSV8S8SelectedOrdinaryTerminal.Success runtime.body}
    (execution : AcceptedRootExecution configuration hidden finiteTape fallback
      runtime accepted) : Oracle :=
  (run (extendFreshTape finiteTape fallback)
    (FSV8S8SelectedOrdinaryTerminal.verifierScript configuration.binding
      runtime.body)
    (projectOracleState execution.functional.prefixes.adversary.finalState)).2

def c1Prefix
    {HiddenTape TapeIdentity Observation : Type}
    {globalOracleCalls steps : Nat}
    {configuration : DynamicConfiguration HiddenTape TapeIdentity Observation
      globalOracleCalls}
    {hidden : HiddenTape} {finiteTape : FreshAnswerTape Block steps}
    {fallback : Block}
    {runtime : FSV8S8SelectedOrdinaryTerminal.Runtime TapeIdentity}
    {accepted : FSV8S8SelectedOrdinaryTerminal.Success runtime.body}
    (execution : AcceptedRootExecution configuration hidden finiteTape fallback
      runtime accepted) : AnswerPrefix :=
  oldRecords (records execution.cuts.c1Cut.log)

def c2Prefix
    {HiddenTape TapeIdentity Observation : Type}
    {globalOracleCalls steps : Nat}
    {configuration : DynamicConfiguration HiddenTape TapeIdentity Observation
      globalOracleCalls}
    {hidden : HiddenTape} {finiteTape : FreshAnswerTape Block steps}
    {fallback : Block}
    {runtime : FSV8S8SelectedOrdinaryTerminal.Runtime TapeIdentity}
    {accepted : FSV8S8SelectedOrdinaryTerminal.Success runtime.body}
    (execution : AcceptedRootExecution configuration hidden finiteTape fallback
      runtime accepted) : AnswerPrefix :=
  oldRecords (records execution.cuts.postC2.log)

def fullLog
    {HiddenTape TapeIdentity Observation : Type}
    {globalOracleCalls steps : Nat}
    {configuration : DynamicConfiguration HiddenTape TapeIdentity Observation
      globalOracleCalls}
    {hidden : HiddenTape} {finiteTape : FreshAnswerTape Block steps}
    {fallback : Block}
    {runtime : FSV8S8SelectedOrdinaryTerminal.Runtime TapeIdentity}
    {accepted : FSV8S8SelectedOrdinaryTerminal.Success runtime.body}
    (execution : AcceptedRootExecution configuration hidden finiteTape fallback
      runtime accepted) : OrderedRawQueryLog :=
  oldLog (finalOracle execution)

theorem projected_adversary_log_consistent
    {HiddenTape TapeIdentity Observation : Type}
    {globalOracleCalls steps : Nat}
    {configuration : DynamicConfiguration HiddenTape TapeIdentity Observation
      globalOracleCalls}
    {hidden : HiddenTape} {finiteTape : FreshAnswerTape Block steps}
    {fallback : Block}
    {runtime : FSV8S8SelectedOrdinaryTerminal.Runtime TapeIdentity}
    (prefixes : SuccessfulRootMachinePrefixes configuration hidden finiteTape
      fallback runtime) :
    LogConsistent (projectOracleState prefixes.adversary.finalState) := by
  intro event member
  obtain ⟨record, recordMember, rfl⟩ := List.mem_map.mp member
  have segmentMember : record ∈
      AspisK1.V7FsStateRestorationCoupling.historySince emptyOracle
      prefixes.adversary.finalState := by
    simpa [AspisK1.V7FsStateRestorationCoupling.historySince, emptyOracle]
      using recordMember
  have retained := projected_machine_prefix_lookup_retains_segment_answer
    configuration.adversaryLimits .adversary configuration.adversaryFuel
    emptyOracle (configuration.blackBox.start hidden configuration.observation)
    (freshAnswerTapeToList finiteTape) prefixes.adversary record segmentMember
  simpa [projectOracleState, projectedCache, projectRecord] using retained

theorem execution_final_log_consistent
    {HiddenTape TapeIdentity Observation : Type}
    {globalOracleCalls steps : Nat}
    {configuration : DynamicConfiguration HiddenTape TapeIdentity Observation
      globalOracleCalls}
    {hidden : HiddenTape} {finiteTape : FreshAnswerTape Block steps}
    {fallback : Block}
    {runtime : FSV8S8SelectedOrdinaryTerminal.Runtime TapeIdentity}
    {accepted : FSV8S8SelectedOrdinaryTerminal.Success runtime.body}
    (execution : AcceptedRootExecution configuration hidden finiteTape fallback
      runtime accepted) : LogConsistent (finalOracle execution) := by
  exact run_log_consistent (extendFreshTape finiteTape fallback)
    (FSV8S8SelectedOrdinaryTerminal.verifierScript configuration.binding
      runtime.body)
    (projectOracleState execution.functional.prefixes.adversary.finalState)
    (projected_adversary_log_consistent execution.functional.prefixes)

theorem advertised_answer_of_consistent (oracle : Oracle)
    (consistent : LogConsistent oracle) (record : AnswerRecord)
    (member : record ∈ records oracle.log) :
    totalView208 oracle record.1 = record.2 := by
  obtain ⟨event, eventMember, rfl⟩ := List.mem_map.mp member
  have cached := consistent event eventMember
  simp [totalView208, view208, cached]

theorem projected_prefix_included (cut final : Oracle)
    (prefixFact : Prefix cut final) :
    TraceIncludedInLog (rawPrefix (oldRecords (records cut.log)))
      (oldLog final) := by
  obtain ⟨suffix, finalLog⟩ := prefixFact
  intro input member
  have cutMember : input ∈ oldLog cut := by
    simpa [rawPrefix, oldRecords, records, oldLog, Function.comp_def] using member
  obtain ⟨event, eventMember, rfl⟩ := List.mem_map.mp cutMember
  apply List.mem_map.mpr
  refine ⟨event, ?_, rfl⟩
  rw [finalLog]
  exact List.mem_append_left _ eventMember

structure ProducedPrefixes
    {HiddenTape TapeIdentity Observation : Type}
    {globalOracleCalls steps : Nat}
    {configuration : DynamicConfiguration HiddenTape TapeIdentity Observation
      globalOracleCalls}
    {hidden : HiddenTape} {finiteTape : FreshAnswerTape Block steps}
    {fallback : Block}
    {runtime : FSV8S8SelectedOrdinaryTerminal.Runtime TapeIdentity}
    {accepted : FSV8S8SelectedOrdinaryTerminal.Success runtime.body}
    (execution : AcceptedRootExecution configuration hidden finiteTape fallback
      runtime accepted) : Type where
  wire : AspisV8.SelectedWireBytes.Wire
  wireParsed : AspisV8.SelectedWireBytes.parse
    (runtime.body.map UInt8.toFin) = some wire
  semanticWire : execution.cuts.wire = SameBodySemanticWire.ofSelected wire
  c1Answers : ∀ record ∈ c1Prefix execution,
    oldView (finalOracle execution) record.1 = record.2
  c2Answers : ∀ record ∈ c2Prefix execution,
    oldView (finalOracle execution) record.1 = record.2
  c1Included : TraceIncludedInLog (rawPrefix (c1Prefix execution))
    (fullLog execution)
  c2Included : TraceIncludedInLog (rawPrefix (c2Prefix execution))
    (fullLog execution)

theorem accepted_execution_constructs_prefixes
    {HiddenTape TapeIdentity Observation : Type}
    {globalOracleCalls steps : Nat}
    {configuration : DynamicConfiguration HiddenTape TapeIdentity Observation
      globalOracleCalls}
    {hidden : HiddenTape} {finiteTape : FreshAnswerTape Block steps}
    {fallback : Block}
    {runtime : FSV8S8SelectedOrdinaryTerminal.Runtime TapeIdentity}
    {accepted : FSV8S8SelectedOrdinaryTerminal.Success runtime.body}
    (execution : AcceptedRootExecution configuration hidden finiteTape fallback
      runtime accepted) : Nonempty (ProducedPrefixes execution) := by
  obtain ⟨wire, parsed, semanticWire⟩ :=
    SameBodySemanticWire.parse_success runtime.body execution.cuts.wire
      execution.cuts.parsed
  have consistent := execution_final_log_consistent execution
  have answers1 : ∀ record ∈ records execution.cuts.c1Cut.log,
      totalView208 (finalOracle execution) record.1 = record.2 := by
    intro record member
    apply advertised_answer_of_consistent (finalOracle execution) consistent
    obtain ⟨suffix, finalExact⟩ := execution.c1ToFinal
    apply List.mem_map.mpr
    obtain ⟨event, eventMember, rfl⟩ := List.mem_map.mp member
    refine ⟨event, ?_, rfl⟩
    unfold finalOracle
    rw [finalExact]
    exact List.mem_append_left _ eventMember
  have answers2 : ∀ record ∈ records execution.cuts.postC2.log,
      totalView208 (finalOracle execution) record.1 = record.2 := by
    intro record member
    apply advertised_answer_of_consistent (finalOracle execution) consistent
    obtain ⟨suffix, finalExact⟩ := execution.c2ToFinal
    apply List.mem_map.mpr
    obtain ⟨event, eventMember, rfl⟩ := List.mem_map.mp member
    refine ⟨event, ?_, rfl⟩
    unfold finalOracle
    rw [finalExact]
    exact List.mem_append_left _ eventMember
  exact ⟨{
    wire := wire,
    wireParsed := parsed,
    semanticWire := semanticWire,
    c1Answers := record_transport _ _ answers1,
    c2Answers := record_transport _ _ answers2,
    c1Included := projected_prefix_included _ _ execution.c1ToFinal,
    c2Included := projected_prefix_included _ _ execution.c2ToFinal
  }⟩

/-- The concrete batch consumed by the authenticated-slot theorem.  Every
input is produced by `execution` and `ProducedPrefixes`; only gamma is the
actual later transcript challenge supplied by the consuming source theorem. -/
def sourcePrefixBatch
    {HiddenTape TapeIdentity Observation : Type}
    {globalOracleCalls steps : Nat}
    {configuration : DynamicConfiguration HiddenTape TapeIdentity Observation
      globalOracleCalls}
    {hidden : HiddenTape} {finiteTape : FreshAnswerTape Block steps}
    {fallback : Block}
    {runtime : FSV8S8SelectedOrdinaryTerminal.Runtime TapeIdentity}
    {accepted : FSV8S8SelectedOrdinaryTerminal.Success runtime.body}
    {execution : AcceptedRootExecution configuration hidden finiteTape fallback
      runtime accepted}
    (produced : ProducedPrefixes execution)
    (gamma : AspisV8.SameBodyAuthenticatedSlots.K) :=
  AspisV8.SameBodyAuthenticatedSlots.prefixBatch (c1Prefix execution)
    (c2Prefix execution) produced.wire gamma

#print axioms projected_adversary_log_consistent
#print axioms execution_final_log_consistent
#print axioms projected_prefix_included
#print axioms accepted_execution_constructs_prefixes

end
end AspisV8Completion.FSV8S8AuthenticatedPrefixProducer
