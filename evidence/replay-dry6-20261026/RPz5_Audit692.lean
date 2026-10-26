import Lean
import ComposedContinuationSpecM10
import AllocatedContinuationM10
import BinFrameConstructionWork
import FrameConstructorAllocationM10
import BinFrameLookupWork
import BinFrameReplayTotalWork
import FrameReplayAllocationM10
import BinRecoveryAddressWork
import RecoveryWalkAllocationM10
import BinPublicRecoveryStageWork
import BinPublicRecoverySharedStageM10
import PublicRecoveryAllocationM10
import RawRecordedEagerExtractorReadsBin
import CostedExtractorStagesM10
import CubicAllocationLiftM10
import CubicFieldBoundM10
import GSScalarBatchJobsM10
import RRRecoveryJobsM10
import GSActualBankJobsM10
import GSActualByteJobsM10
import RawExtractorFixedCubicM10
import CostedAllocationLedgerM10
import ActualExtractorStagesM10
import ActualAllocationExtractorM10
import ActualResourceEvalM10
import ActualCostedExtractorM10
import ActualResourceBoundsM10
import ActualLedgerSideBoundsM10
import ClosedAllocationLedgerM10
import OraclePortHeadlineDVC7
import OraclePortFrozen2Headline
import Port1_CanonicalHeadline
import Frozen2StartChargePrefix
import Frozen2StartChargeCompletion
import Frozen2StartChargeClean
import Frozen2StartChargeProbability
import StartChargeNumeric
import OraclePortHeadlineFrozen2PerAttempt
import Port1_CarrierObstruction
import Uni_CanonicalPerAttempt
import EndP_Endpoint
import Port8EFF_NativeReader
import Par_Parameters
import SAQ_RecordDecode
import SAQ_LineAlgebra
import SAQ_LineCanonical
import SAQ_LineChannels
import SAQ_LineJoin
import SAQ_LineQuery
import SAQ_Decoder
import SAQ_Geometry
import SAQ_Domain
import SAQ_Inverse
import SAQ_GeometrySource
import SAQ_Constructor
import Hist_Authority
import ExtractedMaskLinearStep
import ExtractedMaskLinearLoop
import ExtractedMaskScalarMul
import ExtractedMaskScalarExact
import ExtractedMaskLinears
import ExtractedMaskLinearRecurrence
import ExtractedMaskLinearMomentBridge
import ExtractedMaskLinearsExact
import ExtractedMaskNeg
import ExtractedMaskBasisComponents
import ExtractedMaskTowerBasis
import ExtractedMaskTowerBasisExact
import ExtractedMaskCoefficientArray
import ExtractedMaskCoefficientSchedule
import ExtractedMaskCoefficientStep
import ExtractedMaskForwardRange
import ExtractedMaskCoefficientLoop0
import ExtractedMaskCoefficientLoop1
import ExtractedMaskHornerLoop
import ExtractedMaskHornerPolynomial
import ExtractedMaskHornerCaller
import ExtractedMaskCM31Square
import ExtractedMaskSquareArithmetic
import ExtractedMaskCM31SquareEqMul
import ExtractedMaskQM31Square
import ExtractedMaskQM31SquareExact
import ExtractedMaskPower26
import ExtractedMaskConstants
import ExtractedMaskCallerModel
import SAF_Returns
import F3N_CheckpointRun
import F3L_AccumulatorExt
import F3L_WriterAccumulator
import SAP_WrapperCanonical
import SAP_InputQuery
import FIn_Staged
import SAG_DotWeights
import SAG_DotLaw
import Hist_ArgumentCuts
import P2P_Origin
import NP6_ClaimsModel
import NP6_ClaimsSuccess
import NP6_ClaimsMain
import NP6_ClaimsRun

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `ComposedContinuationSpecM10, `AllocatedContinuationM10, `BinFrameConstructionWork, `FrameConstructorAllocationM10, `BinFrameLookupWork, `BinFrameReplayTotalWork, `FrameReplayAllocationM10, `BinRecoveryAddressWork, `RecoveryWalkAllocationM10, `BinPublicRecoveryStageWork, `BinPublicRecoverySharedStageM10, `PublicRecoveryAllocationM10, `RawRecordedEagerExtractorReadsBin, `CostedExtractorStagesM10, `CubicAllocationLiftM10, `CubicFieldBoundM10, `GSScalarBatchJobsM10, `RRRecoveryJobsM10, `GSActualBankJobsM10, `GSActualByteJobsM10, `RawExtractorFixedCubicM10, `CostedAllocationLedgerM10, `ActualExtractorStagesM10, `ActualAllocationExtractorM10, `ActualResourceEvalM10, `ActualCostedExtractorM10, `ActualResourceBoundsM10, `ActualLedgerSideBoundsM10, `ClosedAllocationLedgerM10, `OraclePortHeadlineDVC7, `OraclePortFrozen2Headline, `Port1_CanonicalHeadline, `Frozen2StartChargePrefix, `Frozen2StartChargeCompletion, `Frozen2StartChargeClean, `Frozen2StartChargeProbability, `StartChargeNumeric, `OraclePortHeadlineFrozen2PerAttempt, `Port1_CarrierObstruction, `Uni_CanonicalPerAttempt, `EndP_Endpoint, `Port8EFF_NativeReader, `Par_Parameters, `SAQ_RecordDecode, `SAQ_LineAlgebra, `SAQ_LineCanonical, `SAQ_LineChannels, `SAQ_LineJoin, `SAQ_LineQuery, `SAQ_Decoder, `SAQ_Geometry, `SAQ_Domain, `SAQ_Inverse, `SAQ_GeometrySource, `SAQ_Constructor, `Hist_Authority, `ExtractedMaskLinearStep, `ExtractedMaskLinearLoop, `ExtractedMaskScalarMul, `ExtractedMaskScalarExact, `ExtractedMaskLinears, `ExtractedMaskLinearRecurrence, `ExtractedMaskLinearMomentBridge, `ExtractedMaskLinearsExact, `ExtractedMaskNeg, `ExtractedMaskBasisComponents, `ExtractedMaskTowerBasis, `ExtractedMaskTowerBasisExact, `ExtractedMaskCoefficientArray, `ExtractedMaskCoefficientSchedule, `ExtractedMaskCoefficientStep, `ExtractedMaskForwardRange, `ExtractedMaskCoefficientLoop0, `ExtractedMaskCoefficientLoop1, `ExtractedMaskHornerLoop, `ExtractedMaskHornerPolynomial, `ExtractedMaskHornerCaller, `ExtractedMaskCM31Square, `ExtractedMaskSquareArithmetic, `ExtractedMaskCM31SquareEqMul, `ExtractedMaskQM31Square, `ExtractedMaskQM31SquareExact, `ExtractedMaskPower26, `ExtractedMaskConstants, `ExtractedMaskCallerModel, `SAF_Returns, `F3N_CheckpointRun, `F3L_AccumulatorExt, `F3L_WriterAccumulator, `SAP_WrapperCanonical, `SAP_InputQuery, `FIn_Staged, `SAG_DotWeights, `SAG_DotLaw, `Hist_ArgumentCuts, `P2P_Origin, `NP6_ClaimsModel, `NP6_ClaimsSuccess, `NP6_ClaimsMain, `NP6_ClaimsRun ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    logInfo m!"RPZ5_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, c) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if c.isAxiom then
        logInfo m!"RPZ5_AXIOM {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString)]).compress}"
      if selected.contains owner && n.hash.toNat % 1 == 0 then
        let debugPrefixes := #["AspisR1RecordParser.r1_wire.Error.Insts.CoreFmtDebug", "AspisR1PrefixAggregateParser.r1_wire.Error.Insts.CoreFmtDebug"]
        let refs := c.type.getUsedConstants ++ (((c.value? true).map (fun e => e.getUsedConstants)).getD #[])
        for ref in refs do
          if debugPrefixes.any (fun p => ref.toString == p || ref.toString.startsWith (p ++ ".")) then
            logInfo m!"RPZ5_DEBUG_REF {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("reference", toJson ref.toString)]).compress}"
        let axs ← collectAxioms n
        logInfo m!"RPZ5_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPZ5_AUDIT_COMPLETE declarations={count} modules={selected.size}"
