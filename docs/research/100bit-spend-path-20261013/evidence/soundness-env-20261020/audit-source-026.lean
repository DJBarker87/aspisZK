import Lean
import R1PublicSourceRawSuccess
import PublicRawCoreAgreement
import PublicRawAmountGuardAgreement
import R1PublicSourceBoundary
import RawPublicInitRecovery
import RawPublicInitParser
import InitialPublicWalk
import InitialPublicWalkCells
import InitialPublicWalkTrace
import SemanticPublicSelection
import EarlyPublicSelection
import R1UnifiedSemanticFacts
import R1UnifiedSemanticActualView
import R1QueryOwnFollow
import R1PrefixNextTrace
import R1UnifiedSemanticInjection
import R1UnifiedFramework
import R1UnifiedOrdinaryFirstCell
import R1UnifiedSemanticCase
import EarlyPublicExperiment
import R1UnifiedReseedView
import R1ReseedOwnFollow
import R1ReseedTrace
import R1PrefixReseedTrace
import R1UnifiedReseedInjection
import R1UnifiedReseedCase
import EarlyPublicSpecialCases
import R1UnifiedPayloadZero
import R1UnifiedCanonicalProver
import EarlyPublicTotalCase

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`R1PublicSourceRawSuccess, `PublicRawCoreAgreement, `PublicRawAmountGuardAgreement, `R1PublicSourceBoundary, `RawPublicInitRecovery, `RawPublicInitParser, `InitialPublicWalk, `InitialPublicWalkCells, `InitialPublicWalkTrace, `SemanticPublicSelection, `EarlyPublicSelection, `R1UnifiedSemanticFacts, `R1UnifiedSemanticActualView, `R1QueryOwnFollow, `R1PrefixNextTrace, `R1UnifiedSemanticInjection, `R1UnifiedFramework, `R1UnifiedOrdinaryFirstCell, `R1UnifiedSemanticCase, `EarlyPublicExperiment, `R1UnifiedReseedView, `R1ReseedOwnFollow, `R1ReseedTrace, `R1PrefixReseedTrace, `R1UnifiedReseedInjection, `R1UnifiedReseedCase, `EarlyPublicSpecialCases, `R1UnifiedPayloadZero, `R1UnifiedCanonicalProver, `EarlyPublicTotalCase]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
