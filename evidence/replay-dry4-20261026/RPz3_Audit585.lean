import Lean
import RawCutLiteralQueryOrder
import TraceAppend
import R1TraceAppend
import R1FollowAppend
import OracleProgramLawExt
import LiteralAdaptiveClassifierHitToDecodedChain
import LiteralNoHitFromTranscriptAlignment
import RawChecksHitFromTransport
import R1PublicByteCodec
import R1PublicByteCodecLaws
import PublicCodecAgreement
import AspisR1PublicSerializer.Types
import AspisR1PublicSerializer.Funs
import PublicSerializerFieldsRefinement431
import PublicSerializerSuccess431
import PublicSerializerFrontier431
import PublicSerializerWhole431
import PublicRawCore
import PublicExtractedRawBridge431
import AspisR1WithdrawalValidation.Types
import AspisR1WithdrawalValidation.Funs
import WithdrawalValidationAmount431
import PublicRawAmountGuard
import WithdrawalCarrierBridge431
import R1PublicSourceRaw
import R1PublicCodecAgreement
import R1PublicSourceRawMap
import R1PublicSourceRawSuccess
import PublicRawCoreAgreement
import PublicRawAmountGuardAgreement
import R1PublicSourceBoundary
import ExtractedPublicCheckedBridge432
import BinMerkle32Path
import BinMerkleNodeCodec
import BinRawByteCollisionTargets
import BinCombinedMerkleCollision
import QueryScanExhaustion
import QueryScanModelFailure
import QvStage1Count
import QvStage2Count
import BinMerkleTable
import BinMerkleRecovery
import BinMerkle32Leaf
import BinMerkleLeafRecovery
import BinMerkleLeafCodec
import BinMerkleRecordedLog
import BinMerkleTraceInputs
import BinMerkleLogRecovery
import BinMerkleProgram
import BinRawByteCutRecovery
import BinMerkleWalkWitness
import BinRecordedRecoveryWitness
import BinMerkleLogExtension
import BinRawByteCutStability
import BinMultiproof
import WireBindingRecordCodec
import SharedBinaryRecordGrammar
import BinGrammar
import BinSharedGrammarBridge
import R1VerifierCallBudget
import RawDigestLogCarrier
import QueryScanAbortAccounting
import RWireRawBoundedCollision
import RWireRawCutLiteralQueryOrder
import RWireMerkleNodeLookupExt
import RWireMerkleNodeRecordUnique
import RWireMerkleLeafLookupExt
import RWireMerkleLeafRecordUnique
import RWireMerkleLogExt
import RWireRawByteCutTable
import OraclePortPureOutputC7
import MultiproofParserRef.Types
import MultiproofParserRef.Funs
import MultiproofConeWordScan
import R1ExtractedM31Parser
import R22ControlBounds
import OraclePortStdBuilder
import AspisR1Qm31ArithmeticProbe.Types
import AspisR1Qm31ArithmeticProbe.Funs
import ExtractedCurrentReducerOps
import S7Kani2AccumulatorLoop
import S7Kani2BasisLoop
import AspisV8R17.RawReducerNat
import ExtractedCurrentReducer
import S7Kani2PrefixLoop
import ExtractedCurrentM31AddSub
import S7Kani3BasisOuter
import S7Kani3BasisTotal
import S7JoinBasisBlock
import S7JoinBasisIdentity
import S7JoinBasisHighBit
import LineFold
import FoldRuntimeAlgebra
import ExtractedCurrentTowerAdd
import ExtractedCurrentCM31Mul
import ExtractedCurrentQM31Mul
import AspisV8R17.QM31WordFormulas
import AspisV8R17.QM31WordResidues
import AspisV8R17.QuadraticTowerOperations
import AspisV8R17.QM31WordTower

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RawCutLiteralQueryOrder, `TraceAppend, `R1TraceAppend, `R1FollowAppend, `OracleProgramLawExt, `LiteralAdaptiveClassifierHitToDecodedChain, `LiteralNoHitFromTranscriptAlignment, `RawChecksHitFromTransport, `R1PublicByteCodec, `R1PublicByteCodecLaws, `PublicCodecAgreement, `AspisR1PublicSerializer.Types, `AspisR1PublicSerializer.Funs, `PublicSerializerFieldsRefinement431, `PublicSerializerSuccess431, `PublicSerializerFrontier431, `PublicSerializerWhole431, `PublicRawCore, `PublicExtractedRawBridge431, `AspisR1WithdrawalValidation.Types, `AspisR1WithdrawalValidation.Funs, `WithdrawalValidationAmount431, `PublicRawAmountGuard, `WithdrawalCarrierBridge431, `R1PublicSourceRaw, `R1PublicCodecAgreement, `R1PublicSourceRawMap, `R1PublicSourceRawSuccess, `PublicRawCoreAgreement, `PublicRawAmountGuardAgreement, `R1PublicSourceBoundary, `ExtractedPublicCheckedBridge432, `BinMerkle32Path, `BinMerkleNodeCodec, `BinRawByteCollisionTargets, `BinCombinedMerkleCollision, `QueryScanExhaustion, `QueryScanModelFailure, `QvStage1Count, `QvStage2Count, `BinMerkleTable, `BinMerkleRecovery, `BinMerkle32Leaf, `BinMerkleLeafRecovery, `BinMerkleLeafCodec, `BinMerkleRecordedLog, `BinMerkleTraceInputs, `BinMerkleLogRecovery, `BinMerkleProgram, `BinRawByteCutRecovery, `BinMerkleWalkWitness, `BinRecordedRecoveryWitness, `BinMerkleLogExtension, `BinRawByteCutStability, `BinMultiproof, `WireBindingRecordCodec, `SharedBinaryRecordGrammar, `BinGrammar, `BinSharedGrammarBridge, `R1VerifierCallBudget, `RawDigestLogCarrier, `QueryScanAbortAccounting, `RWireRawBoundedCollision, `RWireRawCutLiteralQueryOrder, `RWireMerkleNodeLookupExt, `RWireMerkleNodeRecordUnique, `RWireMerkleLeafLookupExt, `RWireMerkleLeafRecordUnique, `RWireMerkleLogExt, `RWireRawByteCutTable, `OraclePortPureOutputC7, `MultiproofParserRef.Types, `MultiproofParserRef.Funs, `MultiproofConeWordScan, `R1ExtractedM31Parser, `R22ControlBounds, `OraclePortStdBuilder, `AspisR1Qm31ArithmeticProbe.Types, `AspisR1Qm31ArithmeticProbe.Funs, `ExtractedCurrentReducerOps, `S7Kani2AccumulatorLoop, `S7Kani2BasisLoop, `AspisV8R17.RawReducerNat, `ExtractedCurrentReducer, `S7Kani2PrefixLoop, `ExtractedCurrentM31AddSub, `S7Kani3BasisOuter, `S7Kani3BasisTotal, `S7JoinBasisBlock, `S7JoinBasisIdentity, `S7JoinBasisHighBit, `LineFold, `FoldRuntimeAlgebra, `ExtractedCurrentTowerAdd, `ExtractedCurrentCM31Mul, `ExtractedCurrentQM31Mul, `AspisV8R17.QM31WordFormulas, `AspisV8R17.QM31WordResidues, `AspisV8R17.QuadraticTowerOperations, `AspisV8R17.QM31WordTower ]
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
