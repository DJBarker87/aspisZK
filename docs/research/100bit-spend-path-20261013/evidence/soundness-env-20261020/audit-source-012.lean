import Lean
import R1UnifiedPayloadValue
import R1UnifiedRecords
import R1UnifiedPayloadStep
import R1UnifiedSteps
import R1UnifiedPhases
import R1RawRecordSplit
import R1UnifiedSemanticRecords
import R1UnifiedChainReads
import R1UnifiedProtocol
import R1UnifiedVerifier
import R1CompletedView
import R1UnifiedRecordCompletion
import R1UnifiedContinuation
import R1UnifiedQueryRun
import R1UnifiedQueryReads
import R1UnifiedTraceReads
import R1UnifiedPrefixedReads
import R1InitialWalkTrace
import R1UnifiedSemanticRecovery
import R1UnifiedSemanticContext
import R1PrefixNextLaw
import R1QueryMissingFacts
import R1TableStateSeparation
import R1PrefixPendingFacts
import R1PrefixRecordFacts
import R1PrefixRecordLength
import R1UnifiedSemanticDecoder
import R1UnifiedReseedDecoder
import R1UnifiedOpeningDecoder
import R1UnifiedSemanticLaw

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`R1UnifiedPayloadValue, `R1UnifiedRecords, `R1UnifiedPayloadStep, `R1UnifiedSteps, `R1UnifiedPhases, `R1RawRecordSplit, `R1UnifiedSemanticRecords, `R1UnifiedChainReads, `R1UnifiedProtocol, `R1UnifiedVerifier, `R1CompletedView, `R1UnifiedRecordCompletion, `R1UnifiedContinuation, `R1UnifiedQueryRun, `R1UnifiedQueryReads, `R1UnifiedTraceReads, `R1UnifiedPrefixedReads, `R1InitialWalkTrace, `R1UnifiedSemanticRecovery, `R1UnifiedSemanticContext, `R1PrefixNextLaw, `R1QueryMissingFacts, `R1TableStateSeparation, `R1PrefixPendingFacts, `R1PrefixRecordFacts, `R1PrefixRecordLength, `R1UnifiedSemanticDecoder, `R1UnifiedReseedDecoder, `R1UnifiedOpeningDecoder, `R1UnifiedSemanticLaw]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
