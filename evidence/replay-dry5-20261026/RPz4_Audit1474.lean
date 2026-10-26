import Lean
import AspisFormal.V5WithoutReplacementQuerySoundness
import AspisFormal.V5FriCoherentCandidateExtraction
import AspisFormal.V5FriConcreteEncoderCommutation
import AspisFormal.V5FriJohnsonListBound
import AspisFormal.V5FriInitialListBound
import AspisFormal.V5FriNaturalBasisRadix4
import AspisFormal.V5FriConcreteEncoderApplicability
import AspisFormal.CircleGroupCardinality
import AspisFormal.V5FriCircleEncoderDistance
import AspisFormal.V5FriInitialCircleEncoderIdentity
import AspisFormal.V5FriReleasedLineGeometry
import AspisFormal.V6OneFoldParameterAudit
import AspisFormal.V6OneFoldCandidateExtraction
import AspisFormal.V6EncoderDistance
import AspisFormal.V7ExactOneFoldDomains
import R1Line18Geometry
import R1NaturalProjection
import R1RepeatedLift
import R1ParentSupport
import AspisFormal.Pool.KnowledgeExtractorInterface
import AspisFormal.V6Width29CorrelatedAgreement
import AspisFormal.V5FriDegreeThreeCorrelatedAgreement
import AspisFormal.V6PublishedTheoremInterfaces
import AspisFormal.Pool.AlgorithmicCircleDecoderV7
import Wide.InitialEncoder
import Wide.FinalEncoder
import R1ConcreteProjection
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
import R1SecondFoldMatched
import R1SecondFoldRestoration
import R1FirstFold
import R1RoundPairing
import R1FoldCoefficientBridge
import R1FirstFoldRestoration
import Wide.BatchSeparation
import R1JointList
import Wide.InitialRoot
import Wide.InitialBranch
import Wide.InitialSelection
import Wide.InitialCurveBranch
import Wide.InitialCurve
import Wide.Initial
import R1InitialResponses
import R1TwoFoldExtraction
import R1FunctionalBatchClean
import R1TwoRoundComparison
import R1TwoRoundPairing
import R1JointFunctionalBinding
import R1FunctionalWeights
import R1ConcreteBinding
import R1MatchingSupport
import Wide.EncoderConjugation
import Wide.SubfieldDescentCore
import R1CandidateDescent
import R1FixedWidthDecoder
import R1FixedWidthSlice
import R1FixedWidthEncoding
import R1RetainedFieldByteCodec
import R1ListFieldCodec
import AspisV8R15.ExactTowerBase
import R1RetainedExactLimbCodec

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `AspisFormal.V5WithoutReplacementQuerySoundness, `AspisFormal.V5FriCoherentCandidateExtraction, `AspisFormal.V5FriConcreteEncoderCommutation, `AspisFormal.V5FriJohnsonListBound, `AspisFormal.V5FriInitialListBound, `AspisFormal.V5FriNaturalBasisRadix4, `AspisFormal.V5FriConcreteEncoderApplicability, `AspisFormal.CircleGroupCardinality, `AspisFormal.V5FriCircleEncoderDistance, `AspisFormal.V5FriInitialCircleEncoderIdentity, `AspisFormal.V5FriReleasedLineGeometry, `AspisFormal.V6OneFoldParameterAudit, `AspisFormal.V6OneFoldCandidateExtraction, `AspisFormal.V6EncoderDistance, `AspisFormal.V7ExactOneFoldDomains, `R1Line18Geometry, `R1NaturalProjection, `R1RepeatedLift, `R1ParentSupport, `AspisFormal.Pool.KnowledgeExtractorInterface, `AspisFormal.V6Width29CorrelatedAgreement, `AspisFormal.V5FriDegreeThreeCorrelatedAgreement, `AspisFormal.V6PublishedTheoremInterfaces, `AspisFormal.Pool.AlgorithmicCircleDecoderV7, `Wide.InitialEncoder, `Wide.FinalEncoder, `R1ConcreteProjection, `Wide.DegreeThreeMatched, `Wide.Cardinality, `Wide.EncoderLinearity, `Wide.GRSConversion, `Wide.MultiplicityThreeGS, `Wide.Interpolation, `Wide.Agreement, `Wide.Factors, `Wide.Smooth, `Wide.Hensel, `Wide.LocalFactors, `Wide.FunctionField, `Wide.PowerSeriesLift, `Wide.RegularWeights, `Wide.RegularRing, `Wide.RegularZeroCount, `Wide.HenselCombinatorics, `Wide.HenselRecurrence, `Wide.RegularEvaluation, `Wide.RegularHensel, `Wide.FactorBudgets, `Wide.HenselWeights, `Wide.HenselIntegralLift, `Wide.HenselSpecialization, `Wide.FiniteBranch, `AspisFormal.K1.V7ExactCorrelatedAgreementIncidence, `Wide.BranchEvaluation, `Wide.AmbientCurve, `Wide.FixedBranchCurve, `Wide.ReleasedLift, `Wide.ConcreteBranch, `AspisFormal.K1.V7ExactCorrelatedAgreementWeightedPigeonhole, `Wide.OuterSelection, `Wide.FinalRoot, `Wide.FinalBranch, `Wide.FinalSelection, `Wide.FinalCurveBranch, `Wide.FinalCurve, `Wide.Terminal, `R1FinalResponses, `R1SecondFoldMatched, `R1SecondFoldRestoration, `R1FirstFold, `R1RoundPairing, `R1FoldCoefficientBridge, `R1FirstFoldRestoration, `Wide.BatchSeparation, `R1JointList, `Wide.InitialRoot, `Wide.InitialBranch, `Wide.InitialSelection, `Wide.InitialCurveBranch, `Wide.InitialCurve, `Wide.Initial, `R1InitialResponses, `R1TwoFoldExtraction, `R1FunctionalBatchClean, `R1TwoRoundComparison, `R1TwoRoundPairing, `R1JointFunctionalBinding, `R1FunctionalWeights, `R1ConcreteBinding, `R1MatchingSupport, `Wide.EncoderConjugation, `Wide.SubfieldDescentCore, `R1CandidateDescent, `R1FixedWidthDecoder, `R1FixedWidthSlice, `R1FixedWidthEncoding, `R1RetainedFieldByteCodec, `R1ListFieldCodec, `AspisV8R15.ExactTowerBase, `R1RetainedExactLimbCodec ]
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
