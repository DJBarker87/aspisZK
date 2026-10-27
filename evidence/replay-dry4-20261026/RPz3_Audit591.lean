import Lean
import PublicParserAllocationM10
import ExtractorStagesM10
import AllocationPublicStageM10
import PublicParsedIndexM10
import CountDominanceM10
import StartChargeHit
import ExtractedRecordByteValue
import StrictLowChunkCodec
import ExtractedPrefixFieldAgreement
import ExtractedRecordStrictCodec
import ExtractedRecordStrictLow
import ExtractedPrefixLoopMap
import ExtractedPrefixRecordAgreement
import ExtractedPrefixParserAgreement
import AspisR1RowShape.Types
import AspisR1RowShape.Funs
import ExtractedRowShape
import ExtractedRecordFraming
import RecordPayloadPartition
import ExtractedRecordHighZero
import ExtractedRecordValidator
import ExtractedRecordPayloadSoundness
import ExtractedPrefixStrictPayload
import ExtractedPrefixSemanticLow
import ExtractedPrefixChunkOrder
import ExtractedPrefixCoefficients
import ExtractedPrefixHeaderBytes
import R1RecordLengthCodec
import R1RecordParserModel
import ExtractedPrefixFrameAgreement
import ExtractedPrefixRowPayload
import ExtractedPrefixTypedFull
import AspisV8R19.InverseFieldSlice
import AspisV8R19.GuardedFieldSlice
import AspisV8R19.ComplexFieldSlice
import AspisV8R19.QuarticFieldSlice
import AspisV8R19.InverseRuntimeMul
import AspisV8R19.CanonicalProduct
import AspisV8R19.GuardedM31Execution
import AspisV8R17.RawReducer
import AspisV8R19.InverseChain
import AspisV8R19.GeneratedInverseLoop
import AspisV8R19.GuardedInverseExecution
import AspisV8R19.NormInverse
import AspisV8R19.ComplexBaseExecution
import AspisV8R19.ComplexInverseExecution
import AspisV8R19.QuarticBaseExecution
import AspisV8R19.PartialProduct
import AspisV8R19.PartialDot
import AspisV8R19.LazyComplexExecution
import AspisV8R19.QuarticInverseExecution
import F3M_SevenTerms
import AspisR1DecodeKFullLoopBodyValueFrame
import AspisR1DecodeKFullLoopReadback
import AspisR1DecodeKFullSuccessReadback
import AspisR1DecodeKFullValueTrace
import AspisR1DecodeKFullSuccessIndexedParser
import F3P_TraceArithmetic
import F3P_Offset
import F3P_TraceInput
import F3P_TraceStart
import F3P_SliceIndex
import F3P_TraceBytes0
import F3P_TraceBytes1
import F3P_TraceBytes2
import F3P_TraceBytes3
import F3P_ListWindow
import F3P_TraceWindow
import ActualDecodeKFieldParserTransport
import ActualDecodeKQMParserTransport
import SAQ_InverseTypes
import SAQ_InverseExplicitMul
import SAQ_SquareRangeFacts
import SAQ_SquareSourceModel
import SAQ_InverseSourceModel
import SAQ_InverseFieldModel
import CurrentWideLinearExact
import SAQ_RawScale

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `PublicParserAllocationM10, `ExtractorStagesM10, `AllocationPublicStageM10, `PublicParsedIndexM10, `CountDominanceM10, `StartChargeHit, `ExtractedRecordByteValue, `StrictLowChunkCodec, `ExtractedPrefixFieldAgreement, `ExtractedRecordStrictCodec, `ExtractedRecordStrictLow, `ExtractedPrefixLoopMap, `ExtractedPrefixRecordAgreement, `ExtractedPrefixParserAgreement, `AspisR1RowShape.Types, `AspisR1RowShape.Funs, `ExtractedRowShape, `ExtractedRecordFraming, `RecordPayloadPartition, `ExtractedRecordHighZero, `ExtractedRecordValidator, `ExtractedRecordPayloadSoundness, `ExtractedPrefixStrictPayload, `ExtractedPrefixSemanticLow, `ExtractedPrefixChunkOrder, `ExtractedPrefixCoefficients, `ExtractedPrefixHeaderBytes, `R1RecordLengthCodec, `R1RecordParserModel, `ExtractedPrefixFrameAgreement, `ExtractedPrefixRowPayload, `ExtractedPrefixTypedFull, `AspisV8R19.InverseFieldSlice, `AspisV8R19.GuardedFieldSlice, `AspisV8R19.ComplexFieldSlice, `AspisV8R19.QuarticFieldSlice, `AspisV8R19.InverseRuntimeMul, `AspisV8R19.CanonicalProduct, `AspisV8R19.GuardedM31Execution, `AspisV8R17.RawReducer, `AspisV8R19.InverseChain, `AspisV8R19.GeneratedInverseLoop, `AspisV8R19.GuardedInverseExecution, `AspisV8R19.NormInverse, `AspisV8R19.ComplexBaseExecution, `AspisV8R19.ComplexInverseExecution, `AspisV8R19.QuarticBaseExecution, `AspisV8R19.PartialProduct, `AspisV8R19.PartialDot, `AspisV8R19.LazyComplexExecution, `AspisV8R19.QuarticInverseExecution, `F3M_SevenTerms, `AspisR1DecodeKFullLoopBodyValueFrame, `AspisR1DecodeKFullLoopReadback, `AspisR1DecodeKFullSuccessReadback, `AspisR1DecodeKFullValueTrace, `AspisR1DecodeKFullSuccessIndexedParser, `F3P_TraceArithmetic, `F3P_Offset, `F3P_TraceInput, `F3P_TraceStart, `F3P_SliceIndex, `F3P_TraceBytes0, `F3P_TraceBytes1, `F3P_TraceBytes2, `F3P_TraceBytes3, `F3P_ListWindow, `F3P_TraceWindow, `ActualDecodeKFieldParserTransport, `ActualDecodeKQMParserTransport, `SAQ_InverseTypes, `SAQ_InverseExplicitMul, `SAQ_SquareRangeFacts, `SAQ_SquareSourceModel, `SAQ_InverseSourceModel, `SAQ_InverseFieldModel, `CurrentWideLinearExact, `SAQ_RawScale ]
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
