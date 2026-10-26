import Lean
import R1PublicByteCursor
import PublicOptionShape
import R1SemanticPublicWire
import R1SemanticPublicWireRoundTrip
import R1SemanticPublicWireSound
import R1SemanticPublicWireInjective
import R1SemanticPublicByteBinding
import R1SemanticPublicWireSurjective
import R1SemanticPublicCodecComplete
import R1SelectedTranscriptParams
import R0C.V3.BS
import R0C.V3.Gen
import R1AllAddressFiatShamir
import AllAddressCollision
import AllAddressCollisionTrace
import R1CombinedMerkleTargets
import RawByteCollisionTargets
import RawByteCutRecovery
import RawByteCutStability
import R1RecordFrameCodec
import R1SemanticCoefficientCodec
import R1PrefixedStateCodec
import R1SemanticRecordCodec
import R0C.CircleRows
import AspisV8R19.SamplerCirclePolicy
import R0P.CircleSampler
import R0P.SemAccept
import R0P.SemHonest
import R0P.SemDeg
import R0P.SemDegFamilies
import R0P.SemVirtualDeg
import R0P.SemPad
import R0C.V3.BSOk
import R0C.V3.Q22Law
import R0C.OpeningSamplerBounds
import R0C.SlackDensity
import R0C.V3.DuplexQ
import R0C.V3.DuplexQDensity
import R0C.V3.DQChain
import R0C.V3.DQDecodes
import R0C.SlackObstruction
import R0C.SlackBits
import R0C.V3.R0Q
import R0P.MessageDescent
import R0P.SemD3Glue
import R0P.MaskProtocol
import R0P.MaskView
import R1SemanticPayloadView
import R1SelectedSemanticPrefix
import R1SelectedSemanticPrefixFacts
import D18Transport
import R1D18Transport
import R1OutputCopyLinks
import R1OutputNotes
import R1AppendNode
import R1PairCopyLinks
import AspisFormal.Pool.V7PairLeafOccupancy
import R1AppendPair
import R1InputPairCopyLinks
import R1InputPair
import R1SpendValues
import R1SpendSemantics
import R1InputPairSelection
import R1InputWitnessCore
import R1InputWitnessCheck
import R1AppendCopyLinks
import R1AppendPath
import SpendAppendBinding
import R1SpendAppendBinding
import SpendRelation
import R1SpendRelation
import R1SpendDataMap
import R1PublicBaseMap
import R1ExactBaseProjection
import R0P.SemD2Glue
import R0P.MaskD2
import R0P.MaskBadSets
import R0P.MaskDensity
import R0P.SemDuplexDecoder
import R0P.MaskDuplexDecoder
import R0P.MaskSource
import R0P.MaskD2Glue
import R0P.MaskValue
import R1DuplexRewind
import R1DuplexAbsorb
import R1DuplexSeek
import R1DuplexOrder
import R1DuplexPrefixTable
import R1QueryContinuation
import R1QueryTruncation
import R1QuerySelectedPrefix
import R1QueryStateList
import R1QueryCompletion
import R1QueryFirstRead
import R1QueryDecoder
import R1QueryCompletionSupport
import R1QueryDecoderAnswers
import R1BackgroundMeanCongr
import R1QueryNextLaw
import R1InitialSamplerLaw

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `R1PublicByteCursor, `PublicOptionShape, `R1SemanticPublicWire, `R1SemanticPublicWireRoundTrip, `R1SemanticPublicWireSound, `R1SemanticPublicWireInjective, `R1SemanticPublicByteBinding, `R1SemanticPublicWireSurjective, `R1SemanticPublicCodecComplete, `R1SelectedTranscriptParams, `R0C.V3.BS, `R0C.V3.Gen, `R1AllAddressFiatShamir, `AllAddressCollision, `AllAddressCollisionTrace, `R1CombinedMerkleTargets, `RawByteCollisionTargets, `RawByteCutRecovery, `RawByteCutStability, `R1RecordFrameCodec, `R1SemanticCoefficientCodec, `R1PrefixedStateCodec, `R1SemanticRecordCodec, `R0C.CircleRows, `AspisV8R19.SamplerCirclePolicy, `R0P.CircleSampler, `R0P.SemAccept, `R0P.SemHonest, `R0P.SemDeg, `R0P.SemDegFamilies, `R0P.SemVirtualDeg, `R0P.SemPad, `R0C.V3.BSOk, `R0C.V3.Q22Law, `R0C.OpeningSamplerBounds, `R0C.SlackDensity, `R0C.V3.DuplexQ, `R0C.V3.DuplexQDensity, `R0C.V3.DQChain, `R0C.V3.DQDecodes, `R0C.SlackObstruction, `R0C.SlackBits, `R0C.V3.R0Q, `R0P.MessageDescent, `R0P.SemD3Glue, `R0P.MaskProtocol, `R0P.MaskView, `R1SemanticPayloadView, `R1SelectedSemanticPrefix, `R1SelectedSemanticPrefixFacts, `D18Transport, `R1D18Transport, `R1OutputCopyLinks, `R1OutputNotes, `R1AppendNode, `R1PairCopyLinks, `AspisFormal.Pool.V7PairLeafOccupancy, `R1AppendPair, `R1InputPairCopyLinks, `R1InputPair, `R1SpendValues, `R1SpendSemantics, `R1InputPairSelection, `R1InputWitnessCore, `R1InputWitnessCheck, `R1AppendCopyLinks, `R1AppendPath, `SpendAppendBinding, `R1SpendAppendBinding, `SpendRelation, `R1SpendRelation, `R1SpendDataMap, `R1PublicBaseMap, `R1ExactBaseProjection, `R0P.SemD2Glue, `R0P.MaskD2, `R0P.MaskBadSets, `R0P.MaskDensity, `R0P.SemDuplexDecoder, `R0P.MaskDuplexDecoder, `R0P.MaskSource, `R0P.MaskD2Glue, `R0P.MaskValue, `R1DuplexRewind, `R1DuplexAbsorb, `R1DuplexSeek, `R1DuplexOrder, `R1DuplexPrefixTable, `R1QueryContinuation, `R1QueryTruncation, `R1QuerySelectedPrefix, `R1QueryStateList, `R1QueryCompletion, `R1QueryFirstRead, `R1QueryDecoder, `R1QueryCompletionSupport, `R1QueryDecoderAnswers, `R1BackgroundMeanCongr, `R1QueryNextLaw, `R1InitialSamplerLaw ]
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
