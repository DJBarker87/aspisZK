import Lean
import R0FS.Verifier
import R0FS.Protocol
import R0FS.Hypotheses
import R0C.OpeningSamplerBounds
import FS2.DuplexDecodes
import R0FS.V2
import R0C.SlackStatement
import R0C.ConcreteSlack
import R0C.SlackDensity
import R0C.V3.DuplexQ
import R0C.V3.DuplexQDensity
import R0C.V3.DQChain
import R0C.V3.DQDecodes
import R1QueryDecoderAnswers
import R1BackgroundMeanCongr
import R1QueryNextLaw
import R1InitialSamplerLaw
import R1ReseedSamplerLaw
import R1DuplexSamplers
import R1QuerySampler
import R1QuerySamplerBridge
import R1ParsedStateTrace
import R1OpeningReseedFrame
import R1ReseedBoundary
import R1PrefixedStateCodec
import R1PublicInitParse
import R1InitialWalk
import R1RawRoundDecode
import R1IndexedMessage
import R1RowZeroCodec
import R1CarryLast
import R1RawRoundCompletion
import R1PrefixAnswers
import R1JointPrefixAnswers
import R1JointNextLaw
import R1TranscriptView
import R1UnifiedSampler
import R0C.SemStatement
import R0P.Core
import R0P.PoseidonConstants
import R0P.CoreExt
import R0P.Path
import R0P.Poseidon
import R0P.Positivity
import R0P.Value
import R0P.Positive
import R0P.PositivityWired
import R0P.CopyConstants
import R0P.Copy
import R0P.PositivityChain
import R0P.Schedule
import R0P.EmptyRoots
import R0P.Digest
import R0P.Semantics
import R0P.SemSource
import R0P.SemView
import R0P.Sumcheck
import R0P.Zerocheck
import R0P.Occupancy
import R0P.Asset
import R0P.LaneMap
import R0P.SemDecision
import R0P.CopyInputLinks
import R0P.Extraction
import R0P.SemAssembly
import R0P.CopyRegistry
import R0P.LogUpFrac
import R0P.LogUpCompress
import R0P.SemBadSets
import R0P.LogUpAssembly
import R0P.LogUpChain
import R0P.SemClosed
import R0P.SemRounds
import R0P.SemD3
import R0P.SemD2
import R1SelectedChallengeMapCore
import R1PublicFieldBlockCodec
import R1PublicIndexCodec
import R1PublicIndexListCodec
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
import R1LiteralTranscript
import R1AllAddressFiatShamir
import AllAddressCollision
import AllAddressCollisionTrace
import R1CombinedMerkleTargets
import RawByteCollisionTargets
import RawByteCutRecovery
import RawByteCutStability
import CanonicalCutEnrichedTranscript
import R1RecordFrameCodec
import R1SemanticCoefficientCodec

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `R0FS.Verifier, `R0FS.Protocol, `R0FS.Hypotheses, `R0C.OpeningSamplerBounds, `FS2.DuplexDecodes, `R0FS.V2, `R0C.SlackStatement, `R0C.ConcreteSlack, `R0C.SlackDensity, `R0C.V3.DuplexQ, `R0C.V3.DuplexQDensity, `R0C.V3.DQChain, `R0C.V3.DQDecodes, `R1QueryDecoderAnswers, `R1BackgroundMeanCongr, `R1QueryNextLaw, `R1InitialSamplerLaw, `R1ReseedSamplerLaw, `R1DuplexSamplers, `R1QuerySampler, `R1QuerySamplerBridge, `R1ParsedStateTrace, `R1OpeningReseedFrame, `R1ReseedBoundary, `R1PrefixedStateCodec, `R1PublicInitParse, `R1InitialWalk, `R1RawRoundDecode, `R1IndexedMessage, `R1RowZeroCodec, `R1CarryLast, `R1RawRoundCompletion, `R1PrefixAnswers, `R1JointPrefixAnswers, `R1JointNextLaw, `R1TranscriptView, `R1UnifiedSampler, `R0C.SemStatement, `R0P.Core, `R0P.PoseidonConstants, `R0P.CoreExt, `R0P.Path, `R0P.Poseidon, `R0P.Positivity, `R0P.Value, `R0P.Positive, `R0P.PositivityWired, `R0P.CopyConstants, `R0P.Copy, `R0P.PositivityChain, `R0P.Schedule, `R0P.EmptyRoots, `R0P.Digest, `R0P.Semantics, `R0P.SemSource, `R0P.SemView, `R0P.Sumcheck, `R0P.Zerocheck, `R0P.Occupancy, `R0P.Asset, `R0P.LaneMap, `R0P.SemDecision, `R0P.CopyInputLinks, `R0P.Extraction, `R0P.SemAssembly, `R0P.CopyRegistry, `R0P.LogUpFrac, `R0P.LogUpCompress, `R0P.SemBadSets, `R0P.LogUpAssembly, `R0P.LogUpChain, `R0P.SemClosed, `R0P.SemRounds, `R0P.SemD3, `R0P.SemD2, `R1SelectedChallengeMapCore, `R1PublicFieldBlockCodec, `R1PublicIndexCodec, `R1PublicIndexListCodec, `R1PublicByteCursor, `PublicOptionShape, `R1SemanticPublicWire, `R1SemanticPublicWireRoundTrip, `R1SemanticPublicWireSound, `R1SemanticPublicWireInjective, `R1SemanticPublicByteBinding, `R1SemanticPublicWireSurjective, `R1SemanticPublicCodecComplete, `R1SelectedTranscriptParams, `R1LiteralTranscript, `R1AllAddressFiatShamir, `AllAddressCollision, `AllAddressCollisionTrace, `R1CombinedMerkleTargets, `RawByteCollisionTargets, `RawByteCutRecovery, `RawByteCutStability, `CanonicalCutEnrichedTranscript, `R1RecordFrameCodec, `R1SemanticCoefficientCodec ]
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
