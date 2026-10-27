import Lean
import R1LiteralSemanticPayloadBridge
import R1LiteralSemanticPairs
import R1LiteralSemanticParserFacts
import R1LiteralSemanticViewComponents
import R1LiteralSemanticTake
import R1LiteralC1Prefix
import R1GenericNoHitIndex
import R1LiteralStageMessageCongr
import R1LiteralReadStability
import R1LiteralOpeningCoherence
import R1LiteralStageFacts
import R1LiteralReadAtFacts
import R1LiteralIndexedPrefix
import R1LiteralSemanticNoHit
import R1LiteralSemanticExcludedLift
import R1LiteralMatchingFacts
import R1LiteralOpeningDataRows
import R1LiteralMatchingSemanticData
import R1CandidateBaseProjection
import PoseidonMap
import R1PoseidonMap
import R1NoteHashMap
import R1AppendBindingMap
import R1SpendRelationMap
import R1SpendBaseDescent
import R1TraceSpendWitness
import R1InputWitness
import R1AppendSemantics
import R1SpendRelationExtraction
import R1ConcreteSpendExtraction
import R1LiteralSpendExtraction
import R0P.MaskSemantics
import R1MaskedSemantic
import R1SemanticCandidateList
import R0P.MaskPrefix
import R0P.MaskNoHit
import R1SemanticHit
import R0P.MaskEarly
import R1SemanticPrefix
import R1LiteralSemanticTerminalBridge
import R1LiteralTerminalSpend
import R1LiteralOpeningBinding
import R1LiteralOpeningGood
import R1LiteralByteRunFacts
import R1LiteralGammaSample
import R1LiteralOpeningRunGood
import R1LiteralQueryReadFacts
import R1LiteralQueryBinding
import R1LiteralRhoBinding
import R1LiteralQueryCurrentRead
import R1LiteralQueryContext
import R1LiteralQueryRhoSupport
import R1LiteralQueryRhoTranscriptSupport
import R1SelectedOpeningPairing
import R1LiteralPairingChecks
import R1LiteralTerminalRunSpend
import R1LiteralAcceptanceTerminal
import RawChecksConstructorScheduleV4
import RawCutRecordedWordsExecutable
import RawTranscriptFrameBytes
import OracleProgramReplay
import RawCutWordsFromView
import RawCutLiteralStateSuccessor
import RawCutLiteralTranscriptSuccessor
import RawCommitmentFrameReplay
import RawCutCommitmentFrames
import RawCommitmentFrameReplayCorrect
import CompPoly.Bivariate.Basic
import CompPoly.Bivariate.ToPoly
import CompPoly.Bivariate.Factor
import CompPoly.Bivariate.FactorMonic
import CompPoly.Univariate.Deriv
import CompPoly.ToMathlib.Polynomial.BivariateDegree
import CompPoly.ToMathlib.Polynomial.BivariateMultiplicity
import CompPoly.Bivariate.Deriv
import CompPoly.Bivariate.GuruswamiSudan.Polynomial
import CompPoly.LinearAlgebra.Dense.Basic
import CompPoly.LinearAlgebra.Dense.RowOps
import CompPoly.LinearAlgebra.Dense.RowOpsCorrectness
import CompPoly.LinearAlgebra.Dense.RrefSemantics
import CompPoly.LinearAlgebra.Dense.RrefShape
import CompPoly.LinearAlgebra.Dense.Kernel
import CompPoly.LinearAlgebra.Dense.KernelInPlace
import CompPoly.LinearAlgebra.Dense.KernelCorrectness
import CompPoly.LinearAlgebra.Dense.KernelInPlaceCorrectness
import CompPoly.LinearAlgebra.Dense
import CompPoly.Bivariate.GuruswamiSudan.Context
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Basic
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Dense.Algorithm
import CompPoly.Bivariate.GuruswamiSudan.PolynomialCorrectness
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Correctness
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Dense.Correctness
import GSInterpolationRowBasis
import GSConstraintCount
import GSInterpolationBudget
import GSInterpolationBackendWitness
import CompPolyFactorCertificate
import CompPolySequentialFactorInvariant
import CompPolyFactorTwoChildBound
import FiniteFieldCompleteRootCertificate

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `R1LiteralSemanticPayloadBridge, `R1LiteralSemanticPairs, `R1LiteralSemanticParserFacts, `R1LiteralSemanticViewComponents, `R1LiteralSemanticTake, `R1LiteralC1Prefix, `R1GenericNoHitIndex, `R1LiteralStageMessageCongr, `R1LiteralReadStability, `R1LiteralOpeningCoherence, `R1LiteralStageFacts, `R1LiteralReadAtFacts, `R1LiteralIndexedPrefix, `R1LiteralSemanticNoHit, `R1LiteralSemanticExcludedLift, `R1LiteralMatchingFacts, `R1LiteralOpeningDataRows, `R1LiteralMatchingSemanticData, `R1CandidateBaseProjection, `PoseidonMap, `R1PoseidonMap, `R1NoteHashMap, `R1AppendBindingMap, `R1SpendRelationMap, `R1SpendBaseDescent, `R1TraceSpendWitness, `R1InputWitness, `R1AppendSemantics, `R1SpendRelationExtraction, `R1ConcreteSpendExtraction, `R1LiteralSpendExtraction, `R0P.MaskSemantics, `R1MaskedSemantic, `R1SemanticCandidateList, `R0P.MaskPrefix, `R0P.MaskNoHit, `R1SemanticHit, `R0P.MaskEarly, `R1SemanticPrefix, `R1LiteralSemanticTerminalBridge, `R1LiteralTerminalSpend, `R1LiteralOpeningBinding, `R1LiteralOpeningGood, `R1LiteralByteRunFacts, `R1LiteralGammaSample, `R1LiteralOpeningRunGood, `R1LiteralQueryReadFacts, `R1LiteralQueryBinding, `R1LiteralRhoBinding, `R1LiteralQueryCurrentRead, `R1LiteralQueryContext, `R1LiteralQueryRhoSupport, `R1LiteralQueryRhoTranscriptSupport, `R1SelectedOpeningPairing, `R1LiteralPairingChecks, `R1LiteralTerminalRunSpend, `R1LiteralAcceptanceTerminal, `RawChecksConstructorScheduleV4, `RawCutRecordedWordsExecutable, `RawTranscriptFrameBytes, `OracleProgramReplay, `RawCutWordsFromView, `RawCutLiteralStateSuccessor, `RawCutLiteralTranscriptSuccessor, `RawCommitmentFrameReplay, `RawCutCommitmentFrames, `RawCommitmentFrameReplayCorrect, `CompPoly.Bivariate.Basic, `CompPoly.Bivariate.ToPoly, `CompPoly.Bivariate.Factor, `CompPoly.Bivariate.FactorMonic, `CompPoly.Univariate.Deriv, `CompPoly.ToMathlib.Polynomial.BivariateDegree, `CompPoly.ToMathlib.Polynomial.BivariateMultiplicity, `CompPoly.Bivariate.Deriv, `CompPoly.Bivariate.GuruswamiSudan.Polynomial, `CompPoly.LinearAlgebra.Dense.Basic, `CompPoly.LinearAlgebra.Dense.RowOps, `CompPoly.LinearAlgebra.Dense.RowOpsCorrectness, `CompPoly.LinearAlgebra.Dense.RrefSemantics, `CompPoly.LinearAlgebra.Dense.RrefShape, `CompPoly.LinearAlgebra.Dense.Kernel, `CompPoly.LinearAlgebra.Dense.KernelInPlace, `CompPoly.LinearAlgebra.Dense.KernelCorrectness, `CompPoly.LinearAlgebra.Dense.KernelInPlaceCorrectness, `CompPoly.LinearAlgebra.Dense, `CompPoly.Bivariate.GuruswamiSudan.Context, `CompPoly.Bivariate.GuruswamiSudan.Interpolation.Basic, `CompPoly.Bivariate.GuruswamiSudan.Interpolation.Dense.Algorithm, `CompPoly.Bivariate.GuruswamiSudan.PolynomialCorrectness, `CompPoly.Bivariate.GuruswamiSudan.Interpolation.Correctness, `CompPoly.Bivariate.GuruswamiSudan.Interpolation.Dense.Correctness, `GSInterpolationRowBasis, `GSConstraintCount, `GSInterpolationBudget, `GSInterpolationBackendWitness, `CompPolyFactorCertificate, `CompPolySequentialFactorInvariant, `CompPolyFactorTwoChildBound, `FiniteFieldCompleteRootCertificate ]
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
