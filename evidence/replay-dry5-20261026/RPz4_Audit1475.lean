import Lean
import R1ExactLeafFieldCodec
import R1MixedLeafEncoding
import R1MixedLeafSlices
import R1MixedLeafDecoder
import R1TypedRecoveredWords
import R1TypedRecoveryStability
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
import AspisV8R19.R443BoundedRejectionMass
import AspisV8R19.R445InitialBlockRejectionLaw
import AspisV8R19.R599CanonicalFieldTuple
import AspisV8R15.ExactTowerFinite
import WideTower
import R0C.ModuloField
import R1WideExactLimbCodec
import R1FoldedLeafCodec
import R1MerkleIndexGeometry
import R1FoldedRecoveredWord
import R1CanonicalTypedOpening
import R1CanonicalCutOpening
import R1LiteralTypedWords
import R1CanonicalCutTypedProjection
import R1CanonicalCutWordProjection
import R1UnifiedSamplerPublic
import FS2.DuplexWalk
import R1DuplexRewind
import R1DuplexAbsorb
import R1DuplexSeek
import R1DuplexOrder
import R1DuplexPrefixTable
import R0C.QueryCounting
import AspisV8R19.R402Q22IndependentLaw
import AspisV8R19.R407Q22CandidateKernel
import AspisV8R19.R409Q22Relabeling
import AspisV8R19.R411EqualLegalQueryMass
import AspisV8R19.Q22SamplerInvariants
import AspisV8R19.R412LegalQueryEnumeration
import AspisV8R19.R417Q22SuccessLaw
import AspisV8R19.GuardedFirstRead
import AspisV8R19.R413GuardedOracleDistance
import R0C.QuerySource
import R0C.QuerySampler
import R0C.V3.Q22Law
import R1QueryContinuation
import R1QueryTruncation
import R1QuerySelectedPrefix
import R1QueryStateList
import R1QueryCompletion
import R1QueryFirstRead
import R1QueryDecoder
import R1QueryCompletionSupport
import R0C.V3.BS
import R0C.V3.Gen
import R0C.V3.BSOk
import R0.Fold
import R0.PolynomialPair
import R0.ChordDegree
import R0.Dot
import R0.RoundNormalization
import R0.RoundCore
import R0.Round
import R0.LinearDual
import R0.ChordImage
import R0.ChordGeometry
import R0.Chord
import R0.FunctionalWeights
import R0.ResponseSelection
import Wide.JointList
import Wide.Instances
import Wide.MatchedInstances
import R0.ListsResponses
import R0.RootCounts
import R0.OpeningWeights
import R0.OpeningDefinitions
import R0.BadSetBounds
import R0.OpeningAlgebra
import R0.FibreRestoration
import Wide.SubfieldDescent
import R0.Binding
import R0.Ledger
import R0.QueryLaw

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `R1ExactLeafFieldCodec, `R1MixedLeafEncoding, `R1MixedLeafSlices, `R1MixedLeafDecoder, `R1TypedRecoveredWords, `R1TypedRecoveryStability, `R1FixedWidthReconstruction, `R1FixedWidthDecodedSlices, `R1StrictWideByteCodec, `R0C.Counting, `R0C.ModuloCounting, `AspisV8R19.OracleFiniteSupport, `AspisV8R19.SourceOraclePrograms, `AspisV8R19.SamplerWords, `AspisV8R19.QM31SamplerProgram, `AspisV8R19.Q22WordScan, `AspisV8R19.Q22SamplerProgram, `AspisV8R19.SamplerOracleLaws, `AspisV8R19.QM31SamplerInvariants, `AspisV8R19.BoundedSamplerWrapper, `AspisV8R19.SamplerWrapperPolicies, `AspisV8R15.CircleChord, `AspisV8R15.ExactTowerChord, `AspisV8R19.SamplerFieldDecode, `AspisV8R19.R406SamplerWordDistribution, `AspisV8R19.R421UniformMasked31Block, `AspisV8R19.R442RejectionAlphabet, `AspisV8R19.R443BoundedRejectionMass, `AspisV8R19.R445InitialBlockRejectionLaw, `AspisV8R19.R599CanonicalFieldTuple, `AspisV8R15.ExactTowerFinite, `WideTower, `R0C.ModuloField, `R1WideExactLimbCodec, `R1FoldedLeafCodec, `R1MerkleIndexGeometry, `R1FoldedRecoveredWord, `R1CanonicalTypedOpening, `R1CanonicalCutOpening, `R1LiteralTypedWords, `R1CanonicalCutTypedProjection, `R1CanonicalCutWordProjection, `R1UnifiedSamplerPublic, `FS2.DuplexWalk, `R1DuplexRewind, `R1DuplexAbsorb, `R1DuplexSeek, `R1DuplexOrder, `R1DuplexPrefixTable, `R0C.QueryCounting, `AspisV8R19.R402Q22IndependentLaw, `AspisV8R19.R407Q22CandidateKernel, `AspisV8R19.R409Q22Relabeling, `AspisV8R19.R411EqualLegalQueryMass, `AspisV8R19.Q22SamplerInvariants, `AspisV8R19.R412LegalQueryEnumeration, `AspisV8R19.R417Q22SuccessLaw, `AspisV8R19.GuardedFirstRead, `AspisV8R19.R413GuardedOracleDistance, `R0C.QuerySource, `R0C.QuerySampler, `R0C.V3.Q22Law, `R1QueryContinuation, `R1QueryTruncation, `R1QuerySelectedPrefix, `R1QueryStateList, `R1QueryCompletion, `R1QueryFirstRead, `R1QueryDecoder, `R1QueryCompletionSupport, `R0C.V3.BS, `R0C.V3.Gen, `R0C.V3.BSOk, `R0.Fold, `R0.PolynomialPair, `R0.ChordDegree, `R0.Dot, `R0.RoundNormalization, `R0.RoundCore, `R0.Round, `R0.LinearDual, `R0.ChordImage, `R0.ChordGeometry, `R0.Chord, `R0.FunctionalWeights, `R0.ResponseSelection, `Wide.JointList, `Wide.Instances, `Wide.MatchedInstances, `R0.ListsResponses, `R0.RootCounts, `R0.OpeningWeights, `R0.OpeningDefinitions, `R0.BadSetBounds, `R0.OpeningAlgebra, `R0.FibreRestoration, `Wide.SubfieldDescent, `R0.Binding, `R0.Ledger, `R0.QueryLaw ]
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
