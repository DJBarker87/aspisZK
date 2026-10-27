import Lean
import AspisFormal.V6OneFoldParameterAudit
import AspisFormal.V6OneFoldCandidateExtraction
import AspisFormal.V6EncoderDistance
import AspisFormal.V7ExactOneFoldDomains
import R1Line18Geometry
import R1RepeatedLift
import AspisFormal.Pool.KnowledgeExtractorInterface
import AspisFormal.V6Width29CorrelatedAgreement
import AspisFormal.V5FriDegreeThreeCorrelatedAgreement
import AspisFormal.V6PublishedTheoremInterfaces
import AspisFormal.Pool.AlgorithmicCircleDecoderV7
import Wide.InitialEncoder
import Wide.FinalEncoder
import Wide.DegreeThreeMatched
import Wide.Cardinality
import Wide.EncoderLinearity
import Wide.GRSConversion
import Wide.MultiplicityThreeGS
import Wide.Interpolation
import Wide.Agreement
import Wide.Factors
import Wide.Smooth
import Wide.Hensel
import Wide.LocalFactors
import Wide.FunctionField
import Wide.PowerSeriesLift
import Wide.RegularWeights
import Wide.RegularRing
import Wide.RegularZeroCount
import Wide.HenselCombinatorics
import Wide.HenselRecurrence
import Wide.RegularEvaluation
import Wide.RegularHensel
import Wide.FactorBudgets
import Wide.HenselWeights
import Wide.HenselIntegralLift
import Wide.HenselSpecialization
import Wide.FiniteBranch
import AspisFormal.K1.V7ExactCorrelatedAgreementIncidence
import Wide.BranchEvaluation
import Wide.AmbientCurve
import Wide.FixedBranchCurve
import Wide.ReleasedLift
import Wide.ConcreteBranch
import AspisFormal.K1.V7ExactCorrelatedAgreementWeightedPigeonhole
import Wide.OuterSelection
import Wide.FinalRoot
import Wide.FinalBranch
import Wide.FinalSelection
import Wide.FinalCurveBranch
import Wide.FinalCurve
import Wide.Terminal
import R1FinalResponses
import R1FirstFold
import Wide.BatchSeparation
import R1JointList
import Wide.InitialRoot
import Wide.InitialBranch
import Wide.InitialSelection
import Wide.InitialCurveBranch
import Wide.InitialCurve
import Wide.Initial
import R1InitialResponses
import R1FunctionalBatchClean
import R1TwoRoundComparison
import R1JointFunctionalBinding
import Wide.EncoderConjugation
import Wide.SubfieldDescentCore
import R1FixedWidthDecoder
import R1FixedWidthSlice
import R1FixedWidthEncoding
import R1RetainedFieldByteCodec
import R1ListFieldCodec
import AspisV8R15.ExactTowerBase
import R1RetainedExactLimbCodec
import R1ExactLeafFieldCodec
import R1MixedLeafEncoding
import R1MixedLeafSlices
import R1MixedLeafDecoder
import R1FixedWidthReconstruction
import R1FixedWidthDecodedSlices
import R1StrictWideByteCodec
import R0C.Counting
import R0C.ModuloCounting
import AspisV8R19.OracleFiniteSupport
import AspisV8R19.SourceOraclePrograms
import AspisV8R19.SamplerWords
import AspisV8R19.QM31SamplerProgram
import AspisV8R19.Q22WordScan
import AspisV8R19.Q22SamplerProgram
import AspisV8R19.SamplerOracleLaws
import AspisV8R19.QM31SamplerInvariants
import AspisV8R19.BoundedSamplerWrapper
import AspisV8R19.SamplerWrapperPolicies
import AspisV8R15.CircleChord
import AspisV8R15.ExactTowerChord
import AspisV8R19.SamplerFieldDecode
import AspisV8R19.R406SamplerWordDistribution
import AspisV8R19.R421UniformMasked31Block
import AspisV8R19.R442RejectionAlphabet

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `AspisFormal.V6OneFoldParameterAudit, `AspisFormal.V6OneFoldCandidateExtraction, `AspisFormal.V6EncoderDistance, `AspisFormal.V7ExactOneFoldDomains, `R1Line18Geometry, `R1RepeatedLift, `AspisFormal.Pool.KnowledgeExtractorInterface, `AspisFormal.V6Width29CorrelatedAgreement, `AspisFormal.V5FriDegreeThreeCorrelatedAgreement, `AspisFormal.V6PublishedTheoremInterfaces, `AspisFormal.Pool.AlgorithmicCircleDecoderV7, `Wide.InitialEncoder, `Wide.FinalEncoder, `Wide.DegreeThreeMatched, `Wide.Cardinality, `Wide.EncoderLinearity, `Wide.GRSConversion, `Wide.MultiplicityThreeGS, `Wide.Interpolation, `Wide.Agreement, `Wide.Factors, `Wide.Smooth, `Wide.Hensel, `Wide.LocalFactors, `Wide.FunctionField, `Wide.PowerSeriesLift, `Wide.RegularWeights, `Wide.RegularRing, `Wide.RegularZeroCount, `Wide.HenselCombinatorics, `Wide.HenselRecurrence, `Wide.RegularEvaluation, `Wide.RegularHensel, `Wide.FactorBudgets, `Wide.HenselWeights, `Wide.HenselIntegralLift, `Wide.HenselSpecialization, `Wide.FiniteBranch, `AspisFormal.K1.V7ExactCorrelatedAgreementIncidence, `Wide.BranchEvaluation, `Wide.AmbientCurve, `Wide.FixedBranchCurve, `Wide.ReleasedLift, `Wide.ConcreteBranch, `AspisFormal.K1.V7ExactCorrelatedAgreementWeightedPigeonhole, `Wide.OuterSelection, `Wide.FinalRoot, `Wide.FinalBranch, `Wide.FinalSelection, `Wide.FinalCurveBranch, `Wide.FinalCurve, `Wide.Terminal, `R1FinalResponses, `R1FirstFold, `Wide.BatchSeparation, `R1JointList, `Wide.InitialRoot, `Wide.InitialBranch, `Wide.InitialSelection, `Wide.InitialCurveBranch, `Wide.InitialCurve, `Wide.Initial, `R1InitialResponses, `R1FunctionalBatchClean, `R1TwoRoundComparison, `R1JointFunctionalBinding, `Wide.EncoderConjugation, `Wide.SubfieldDescentCore, `R1FixedWidthDecoder, `R1FixedWidthSlice, `R1FixedWidthEncoding, `R1RetainedFieldByteCodec, `R1ListFieldCodec, `AspisV8R15.ExactTowerBase, `R1RetainedExactLimbCodec, `R1ExactLeafFieldCodec, `R1MixedLeafEncoding, `R1MixedLeafSlices, `R1MixedLeafDecoder, `R1FixedWidthReconstruction, `R1FixedWidthDecodedSlices, `R1StrictWideByteCodec, `R0C.Counting, `R0C.ModuloCounting, `AspisV8R19.OracleFiniteSupport, `AspisV8R19.SourceOraclePrograms, `AspisV8R19.SamplerWords, `AspisV8R19.QM31SamplerProgram, `AspisV8R19.Q22WordScan, `AspisV8R19.Q22SamplerProgram, `AspisV8R19.SamplerOracleLaws, `AspisV8R19.QM31SamplerInvariants, `AspisV8R19.BoundedSamplerWrapper, `AspisV8R19.SamplerWrapperPolicies, `AspisV8R15.CircleChord, `AspisV8R15.ExactTowerChord, `AspisV8R19.SamplerFieldDecode, `AspisV8R19.R406SamplerWordDistribution, `AspisV8R19.R421UniformMasked31Block, `AspisV8R19.R442RejectionAlphabet ]
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
