import Lean
import RawPublicOpeningWalk
import RawLatePublicSelector
import FullPublicSelection
import FullPublicEarlyCase
import R1UnifiedOpeningRecords
import R1OpeningEndpointCells
import RawPublicOpeningWalkCells
import RawPublicOpeningPrefixTrace
import RawPublicOpeningRecovery
import R1UnifiedQueryView
import FullPublicOpeningCase
import R1TableBeforeOrder
import RawPublicOpeningAnchor
import R1UnifiedPhaseRecords
import R1OpeningPrefixAnchor
import R1OpeningAnchorCells
import R1QueryAnswersFirstRead
import R1JointNextTrace
import R1OpeningQueryTrace
import R1UnifiedRecovery
import RawPublicRhoRecovery
import FullPublicRhoCasePublicAPI
import FullPublicTotalCase
import R1ProgramLabelRestriction
import RawBoundedProgram
import R1UnifiedCanonicalLabels
import TraceBadWitness
import RawBoundedCollision
import R1UnifiedDispatchAddress
import R1UnifiedInitialReads

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`RawPublicOpeningWalk, `RawLatePublicSelector, `FullPublicSelection, `FullPublicEarlyCase, `R1UnifiedOpeningRecords, `R1OpeningEndpointCells, `RawPublicOpeningWalkCells, `RawPublicOpeningPrefixTrace, `RawPublicOpeningRecovery, `R1UnifiedQueryView, `FullPublicOpeningCase, `R1TableBeforeOrder, `RawPublicOpeningAnchor, `R1UnifiedPhaseRecords, `R1OpeningPrefixAnchor, `R1OpeningAnchorCells, `R1QueryAnswersFirstRead, `R1JointNextTrace, `R1OpeningQueryTrace, `R1UnifiedRecovery, `RawPublicRhoRecovery, `FullPublicRhoCasePublicAPI, `FullPublicTotalCase, `R1ProgramLabelRestriction, `RawBoundedProgram, `R1UnifiedCanonicalLabels, `TraceBadWitness, `RawBoundedCollision, `R1UnifiedDispatchAddress, `R1UnifiedInitialReads]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
