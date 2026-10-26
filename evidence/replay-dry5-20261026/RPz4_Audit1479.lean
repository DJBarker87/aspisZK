import Lean
import R1CanonicalAddressEmbedding
import CanonicalRawTrace
import PartialAddressImage
import RawBoundedTrace
import RawBackgroundCompletion
import RawUnifiedDecoder
import LiteralDecoderEnrichment
import RawLiteralDecoderDensity
import RawAdaptiveLiteralDecoder
import R1SemanticBudget
import R1PerAttemptEnvelope
import LiteralBudgetEnvelope
import RawAdaptiveClassifierHitDensity
import DecodedFirstReadUnionBound
import DecodedFirstReadTraceBridge
import DecodedFirstReadReplay
import RawCutCompilerDecoderStartLaw
import CompPoly.Data.List.Lemmas
import CompPoly.Data.Array.Lemmas
import CompPoly.Univariate.Raw.Core
import CompPoly.Univariate.Raw.Ops
import CompPoly.Univariate.Raw.Division
import CompPoly.Univariate.Raw.Proofs
import ActualRawPowCoefficientBudget
import ActualRawLongDivisionCost
import CompPoly.Univariate.Basic
import CompPoly.Univariate.Linear
import CompPoly.Univariate.ToPoly.Core
import CompPoly.Univariate.ToPoly.Equiv
import CompPoly.Univariate.ToPoly.Impl
import CompPoly.Univariate.ToPoly.Degree
import CompPoly.ToMathlib.Polynomial.Div
import CompPoly.Univariate.DivisionCorrectness
import CompPoly.ToMathlib.Order.WithBot
import CompPoly.Univariate.EuclideanAlgorithm
import ActualRawModRemainderCostBridge
import ActualCompPolyGCDCostMirror
import CompPoly.Univariate.BatchEval.Naive
import CompPoly.Univariate.Raw
import CompPoly.Univariate.NTT.Domain
import CompPoly.Data.Fin.BigOperators
import CompPoly.Data.Nat.Bitwise
import CompPoly.Univariate.NTT.Transform
import CompPoly.Univariate.NTT.Forward
import CompPoly.Univariate.NTT.Evaluation
import CompPoly.Univariate.NTT.Inverse
import CompPoly.Univariate.NTT.Kernel
import CompPoly.Univariate.NTT.FastMul
import CompPoly.Univariate.NTT.FastMulLow
import CompPoly.Univariate.NTTFast.Plan
import CompPoly.Univariate.NTTFast.FastMul
import CompPoly.Univariate.NTTFast.Correctness.Basic
import CompPoly.Univariate.NTTFast.Correctness.DIF
import CompPoly.Univariate.NTTFast.Correctness.Radix4DIF
import CompPoly.Univariate.NTTFast.Correctness.Pair
import CompPoly.Univariate.NTTFast.Correctness.Radix4DIT
import CompPoly.Univariate.NTTFast.Correctness.Pipeline
import CompPoly.Univariate.NTTFast.FastMulLow
import CompPoly.Univariate.Raw.Context
import CompPoly.Univariate.Raw.Modular
import ActualRawModRemainderSizeBound
import CompPolyModularRemainderDegree
import ActualModularProductDegreeBound
import ActualRawModRemainderDegreeBridge
import ActualRawLongDivisionCostV4
import RawMulSizeBoundV5
import ActualDivisionStepCostBoundV9
import PrivateDivStepBridgeV2
import ActualLongDivisionTotalCostV2
import ActualScaledDivisorMonic
import ActualRawModCostBound
import ActualCompPolyGCDTotalRemainderCost
import ExtractorPowComplexity
import ActualCompPolyPowCost
import CantorZassenhausPair
import CantorZassenhausSplit
import FiniteFieldModularPower
import CantorZassenhausFastTrial
import CompPolyPolynomialBackendBridge
import CompPolySplitTrial
import CantorZassenhausRetries
import CompPolySplitRetries
import CompPolySplitFactorQuality
import CompPolyFactorRecursion
import CompPolyFactorOracleProgram
import CompPolyFactorMeanTools
import SequentialFreshProgram
import SequentialProgramInvariants
import ProgramQueryCost
import RRProgramTraversal
import RRProgramMeanTools
import RRProgramAbortBound
import RRProgramQueryBound
import RawExtractorCostLedger
import R1LiteralOpeningFunctionalFacts
import R1LiteralOpeningPrefixFacts
import R1LiteralSemanticIndex
import R1TypedPrefixParser
import R1SemanticPrefixCodec
import R1LiteralSemanticCodecBridge

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `R1CanonicalAddressEmbedding, `CanonicalRawTrace, `PartialAddressImage, `RawBoundedTrace, `RawBackgroundCompletion, `RawUnifiedDecoder, `LiteralDecoderEnrichment, `RawLiteralDecoderDensity, `RawAdaptiveLiteralDecoder, `R1SemanticBudget, `R1PerAttemptEnvelope, `LiteralBudgetEnvelope, `RawAdaptiveClassifierHitDensity, `DecodedFirstReadUnionBound, `DecodedFirstReadTraceBridge, `DecodedFirstReadReplay, `RawCutCompilerDecoderStartLaw, `CompPoly.Data.List.Lemmas, `CompPoly.Data.Array.Lemmas, `CompPoly.Univariate.Raw.Core, `CompPoly.Univariate.Raw.Ops, `CompPoly.Univariate.Raw.Division, `CompPoly.Univariate.Raw.Proofs, `ActualRawPowCoefficientBudget, `ActualRawLongDivisionCost, `CompPoly.Univariate.Basic, `CompPoly.Univariate.Linear, `CompPoly.Univariate.ToPoly.Core, `CompPoly.Univariate.ToPoly.Equiv, `CompPoly.Univariate.ToPoly.Impl, `CompPoly.Univariate.ToPoly.Degree, `CompPoly.ToMathlib.Polynomial.Div, `CompPoly.Univariate.DivisionCorrectness, `CompPoly.ToMathlib.Order.WithBot, `CompPoly.Univariate.EuclideanAlgorithm, `ActualRawModRemainderCostBridge, `ActualCompPolyGCDCostMirror, `CompPoly.Univariate.BatchEval.Naive, `CompPoly.Univariate.Raw, `CompPoly.Univariate.NTT.Domain, `CompPoly.Data.Fin.BigOperators, `CompPoly.Data.Nat.Bitwise, `CompPoly.Univariate.NTT.Transform, `CompPoly.Univariate.NTT.Forward, `CompPoly.Univariate.NTT.Evaluation, `CompPoly.Univariate.NTT.Inverse, `CompPoly.Univariate.NTT.Kernel, `CompPoly.Univariate.NTT.FastMul, `CompPoly.Univariate.NTT.FastMulLow, `CompPoly.Univariate.NTTFast.Plan, `CompPoly.Univariate.NTTFast.FastMul, `CompPoly.Univariate.NTTFast.Correctness.Basic, `CompPoly.Univariate.NTTFast.Correctness.DIF, `CompPoly.Univariate.NTTFast.Correctness.Radix4DIF, `CompPoly.Univariate.NTTFast.Correctness.Pair, `CompPoly.Univariate.NTTFast.Correctness.Radix4DIT, `CompPoly.Univariate.NTTFast.Correctness.Pipeline, `CompPoly.Univariate.NTTFast.FastMulLow, `CompPoly.Univariate.Raw.Context, `CompPoly.Univariate.Raw.Modular, `ActualRawModRemainderSizeBound, `CompPolyModularRemainderDegree, `ActualModularProductDegreeBound, `ActualRawModRemainderDegreeBridge, `ActualRawLongDivisionCostV4, `RawMulSizeBoundV5, `ActualDivisionStepCostBoundV9, `PrivateDivStepBridgeV2, `ActualLongDivisionTotalCostV2, `ActualScaledDivisorMonic, `ActualRawModCostBound, `ActualCompPolyGCDTotalRemainderCost, `ExtractorPowComplexity, `ActualCompPolyPowCost, `CantorZassenhausPair, `CantorZassenhausSplit, `FiniteFieldModularPower, `CantorZassenhausFastTrial, `CompPolyPolynomialBackendBridge, `CompPolySplitTrial, `CantorZassenhausRetries, `CompPolySplitRetries, `CompPolySplitFactorQuality, `CompPolyFactorRecursion, `CompPolyFactorOracleProgram, `CompPolyFactorMeanTools, `SequentialFreshProgram, `SequentialProgramInvariants, `ProgramQueryCost, `RRProgramTraversal, `RRProgramMeanTools, `RRProgramAbortBound, `RRProgramQueryBound, `RawExtractorCostLedger, `R1LiteralOpeningFunctionalFacts, `R1LiteralOpeningPrefixFacts, `R1LiteralSemanticIndex, `R1TypedPrefixParser, `R1SemanticPrefixCodec, `R1LiteralSemanticCodecBridge ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    logInfo m!"RPZ4_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, c) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if c.isAxiom then
        logInfo m!"RPZ4_AXIOM {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString)]).compress}"
      if selected.contains owner && n.hash.toNat % 1 == 0 then
        let debugPrefixes := #["AspisR1RecordParser.r1_wire.Error.Insts.CoreFmtDebug", "AspisR1PrefixAggregateParser.r1_wire.Error.Insts.CoreFmtDebug"]
        let refs := c.type.getUsedConstants ++ (((c.value? true).map (fun e => e.getUsedConstants)).getD #[])
        for ref in refs do
          if debugPrefixes.any (fun p => ref.toString == p || ref.toString.startsWith (p ++ ".")) then
            logInfo m!"RPZ4_DEBUG_REF {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("reference", toJson ref.toString)]).compress}"
        let axs ← collectAxioms n
        logInfo m!"RPZ4_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPZ4_AUDIT_COMPLETE declarations={count} modules={selected.size}"
