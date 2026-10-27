import Lean
import M31RetryMassNatCard
import M31RetryFiberNatCardBridge
import M31EightLimbProductCount
import M31RetryFiberUniformNat
import M31RetryOutputMassNat
import M31EightLimbSuccessCount
import M31RetryMassRational
import M31EightLimbOutputLaw
import M31EquivUniformTransport
import M31WideExactPacking
import M31EightLimbAbortBound
import M31ActualEightWideSampler
import M31ActualWideSamplerTapeLaw
import M31PairedWideSamplerLaw
import M31PairedSamplerMass
import M31PairedSamplerRejectBound
import WideExactInitialInverseV5
import WideExactInitialCirclePairInverseV5
import FieldInterpolationNodes
import WideExactGRSInstantiationV5
import R1ComputableTraceWitness
import R1TraceValueDecode
import R1PartialJointList
import R1IncrementalJointCandidates
import R1IncrementalCandidateLoop
import FiniteListCandidateMerge
import AcceptedAdaptiveFiatShamir
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
import R1UnifiedInitialCase
import R1UnifiedOpeningRecovery
import R1UnifiedOpeningView
import R1UnifiedOpeningInjection
import R1UnifiedOpeningCase
import R1QueryChainTraceFacts
import R1PrefixQueryTrace
import R1UnifiedQueryInjection
import R1UnifiedQueryCase
import R1JointActualView
import R1UnifiedRhoInjection
import R1UnifiedExperimentInjection
import R1UnifiedRhoCase
import R1UnifiedDispatchCase
import R1UnifiedTotalCase
import RawByteCutTable
import TableLogRepresentative

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `M31RetryMassNatCard, `M31RetryFiberNatCardBridge, `M31EightLimbProductCount, `M31RetryFiberUniformNat, `M31RetryOutputMassNat, `M31EightLimbSuccessCount, `M31RetryMassRational, `M31EightLimbOutputLaw, `M31EquivUniformTransport, `M31WideExactPacking, `M31EightLimbAbortBound, `M31ActualEightWideSampler, `M31ActualWideSamplerTapeLaw, `M31PairedWideSamplerLaw, `M31PairedSamplerMass, `M31PairedSamplerRejectBound, `WideExactInitialInverseV5, `WideExactInitialCirclePairInverseV5, `FieldInterpolationNodes, `WideExactGRSInstantiationV5, `R1ComputableTraceWitness, `R1TraceValueDecode, `R1PartialJointList, `R1IncrementalJointCandidates, `R1IncrementalCandidateLoop, `FiniteListCandidateMerge, `AcceptedAdaptiveFiatShamir, `RawPublicInitRecovery, `RawPublicInitParser, `InitialPublicWalk, `InitialPublicWalkCells, `InitialPublicWalkTrace, `SemanticPublicSelection, `EarlyPublicSelection, `R1UnifiedSemanticFacts, `R1UnifiedSemanticActualView, `R1QueryOwnFollow, `R1PrefixNextTrace, `R1UnifiedSemanticInjection, `R1UnifiedFramework, `R1UnifiedOrdinaryFirstCell, `R1UnifiedSemanticCase, `EarlyPublicExperiment, `R1UnifiedReseedView, `R1ReseedOwnFollow, `R1ReseedTrace, `R1PrefixReseedTrace, `R1UnifiedReseedInjection, `R1UnifiedReseedCase, `EarlyPublicSpecialCases, `R1UnifiedPayloadZero, `R1UnifiedCanonicalProver, `EarlyPublicTotalCase, `RawPublicOpeningWalk, `RawLatePublicSelector, `FullPublicSelection, `FullPublicEarlyCase, `R1UnifiedOpeningRecords, `R1OpeningEndpointCells, `RawPublicOpeningWalkCells, `RawPublicOpeningPrefixTrace, `RawPublicOpeningRecovery, `R1UnifiedQueryView, `FullPublicOpeningCase, `R1TableBeforeOrder, `RawPublicOpeningAnchor, `R1UnifiedPhaseRecords, `R1OpeningPrefixAnchor, `R1OpeningAnchorCells, `R1QueryAnswersFirstRead, `R1JointNextTrace, `R1OpeningQueryTrace, `R1UnifiedRecovery, `RawPublicRhoRecovery, `FullPublicRhoCasePublicAPI, `FullPublicTotalCase, `R1ProgramLabelRestriction, `RawBoundedProgram, `R1UnifiedCanonicalLabels, `TraceBadWitness, `RawBoundedCollision, `R1UnifiedDispatchAddress, `R1UnifiedInitialReads, `R1UnifiedInitialCase, `R1UnifiedOpeningRecovery, `R1UnifiedOpeningView, `R1UnifiedOpeningInjection, `R1UnifiedOpeningCase, `R1QueryChainTraceFacts, `R1PrefixQueryTrace, `R1UnifiedQueryInjection, `R1UnifiedQueryCase, `R1JointActualView, `R1UnifiedRhoInjection, `R1UnifiedExperimentInjection, `R1UnifiedRhoCase, `R1UnifiedDispatchCase, `R1UnifiedTotalCase, `RawByteCutTable, `TableLogRepresentative ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    logInfo m!"RPZ3_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, c) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if c.isAxiom then
        logInfo m!"RPZ3_AXIOM {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString)]).compress}"
      if selected.contains owner && n.hash.toNat % 1 == 0 then
        let debugPrefixes := #["AspisR1RecordParser.r1_wire.Error.Insts.CoreFmtDebug", "AspisR1PrefixAggregateParser.r1_wire.Error.Insts.CoreFmtDebug"]
        let refs := c.type.getUsedConstants ++ (((c.value? true).map (fun e => e.getUsedConstants)).getD #[])
        for ref in refs do
          if debugPrefixes.any (fun p => ref.toString == p || ref.toString.startsWith (p ++ ".")) then
            logInfo m!"RPZ3_DEBUG_REF {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("reference", toJson ref.toString)]).compress}"
        let axs ← collectAxioms n
        logInfo m!"RPZ3_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPZ3_AUDIT_COMPLETE declarations={count} modules={selected.size}"
